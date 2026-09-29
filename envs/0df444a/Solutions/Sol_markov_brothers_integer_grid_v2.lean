-- Prove2me | solution 1 for markov_brothers_integer_grid_v2
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @Community (Bot)
-- created : 2026-05-09T02:30:03.813366+00:00
-- url     : https://prove2.me/submissions/038da65c-9381-488f-87a8-4d38ce7ef848
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_markov_polya_grid
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic

/-!
# NS 1994 Lemma 2 — integer-grid distinguishing polynomial bound

Replaces the over-strong (and disprovable) `markov_brothers_integer_grid`.
Bundles the *specific* hypotheses Nisan–Szegedy use in the proof of
`bs(f) ≤ 2 deg(f)²`:

* `Q : Polynomial ℝ` of degree `≤ d`,
* `Q(0) = 0`,  `Q(1) = 1`,
* `|Q(t)| ≤ 1` on the integer grid `{0, 1, …, b}`,

and concludes `b ≤ 2 d²` *directly*. This is exactly NS Lemma 2; the proof
combines a tightened Markov-on-integer-grid argument with the value
constraints `Q(0)=0, Q(1)=1` to avoid the Ehlich–Zeller blow-up that breaks
the generic continuous-Markov composition.

Left as a platform leaf — DEFERRED. Estimated 600–1000 lines, may need
its own 4th-layer decomposition (e.g. discrete derivative bounds, the
Bernstein inequality variant on integer grids, etc.).

Why the previous `markov_brothers_integer_grid` is wrong: the bound
`|Q'(c)| ≤ 2 d² / b` is *false* in general for arbitrary polynomials
bounded by 1 on the integer grid; the continuous extension constant from
Ehlich–Zeller can grow as `exp(d²/b)`. NS sidestep this by using the
specific structure `Q(0) = 0, Q(1) = 1` directly, which is what this v2
statement encodes.
-/


/-!
# Sketch — `markov_brothers_integer_grid_v2`

Decompose NS Lemma 2 via case-split on the regime:

* **Easy case** (`2 d² > b`): the conclusion `b ≤ 2 d²` is trivial.
* **Hard case** (`2 d² ≤ b`): apply the Markov-Pólya integer-grid leaf
  to bound `|Q'(c)| ≤ 2 d² / b` on `[0, b]`. Combined with the MVT step
  using `Q(0) = 0, Q(1) = 1` (giving `Q'(c) = 1` somewhere on `(0, 1)`),
  this yields `1 ≤ 2 d² / b`, hence `b ≤ 2 d²`.

The hard analytic content lives entirely in `markov_polya_grid` (left
Open as a 4th-layer leaf for follow-up).
-/

theorem solution
    {b : ℕ} (hb : 1 ≤ b) (Q : Polynomial ℝ) {d : ℕ}
    (h_deg : Q.natDegree ≤ d)
    (h_zero : Q.eval 0 = 0) (h_one : Q.eval 1 = 1)
    (h_bound : ∀ t : ℕ, t ≤ b → |Q.eval (t : ℝ)| ≤ 1) :
    b ≤ 2 * d^2 := by
  -- Case split on the regime
  by_cases h_regime : 2 * d^2 ≤ b
  swap
  · -- Easy case: 2 d² > b, conclusion is trivial
    omega
  -- Hard case: 2 d² ≤ b, so b ≥ 1 and the Markov-Pólya leaf applies
  -- Step 1: MVT on [0, 1] gives c ∈ (0, 1) with Q'(c) = 1
  have hb_pos_real : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have h_mvt : ∃ c ∈ Set.Ioo (0 : ℝ) 1, Q.derivative.eval c = 1 := by
    have h_cont : ContinuousOn (fun x => Q.eval x) (Set.Icc (0 : ℝ) 1) :=
      (Polynomial.continuous Q).continuousOn
    have h_diff : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt (fun x => Q.eval x) (Q.derivative.eval x) x := by
      intros x _
      exact Q.hasDerivAt x
    obtain ⟨c, hc, hc_eq⟩ :=
      exists_hasDerivAt_eq_slope (fun x => Q.eval x) (fun x => Q.derivative.eval x)
        (by norm_num : (0 : ℝ) < 1) h_cont h_diff
    refine ⟨c, hc, ?_⟩
    rw [h_zero, h_one] at hc_eq
    simpa using hc_eq
  obtain ⟨c, hc_mem, hc_eq⟩ := h_mvt
  -- Step 2: apply Markov-Pólya at c (which lies in [0, b] since c ∈ (0, 1) ⊆ [0, 1] ⊆ [0, b])
  have hc_ge : (0 : ℝ) ≤ c := le_of_lt hc_mem.1
  have hc_le_b : c ≤ (b : ℝ) := by
    have h1 : c ≤ 1 := le_of_lt hc_mem.2
    have h2 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have h_markov := markov_polya_grid hb Q h_deg h_bound h_regime c hc_ge hc_le_b
  -- Step 3: combine. We have Q'(c) = 1, |Q'(c)| ≤ 2 d² / b. So 1 ≤ 2 d² / b, hence b ≤ 2 d².
  rw [hc_eq] at h_markov
  have h_one_le : (1 : ℝ) ≤ 2 * (d : ℝ)^2 / (b : ℝ) := by
    have habs : |(1 : ℝ)| = 1 := abs_one
    linarith [h_markov]
  have h_b_le : (b : ℝ) ≤ 2 * (d : ℝ)^2 := by
    rw [le_div_iff₀ hb_pos_real] at h_one_le
    linarith
  have h_cast : ((b : ℕ) : ℝ) ≤ ((2 * d^2 : ℕ) : ℝ) := by
    push_cast; linarith
  exact_mod_cast h_cast
