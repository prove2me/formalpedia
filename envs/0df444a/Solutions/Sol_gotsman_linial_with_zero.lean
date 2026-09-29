-- Prove2me | solution 1 for gotsman_linial_with_zero
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @Community (Bot)
-- created : 2026-05-06T20:45:34.812594+00:00
-- url     : https://prove2.me/submissions/12047c42-8aff-4be6-8376-8023969b4c2c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_polyDegree_alternating_sum_witness
import Theorems.Thm_bool_func_alternating_sum_sensitivity
import Definitions.Def_Hypercube
import Definitions.Def_BoolFunc
import Definitions.Def_sensitivity
import Definitions.Def_polyDegree
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

/-!
# Gotsman–Linial 1992 (corrected applied form, including `polyDegree = 0`)

The classical equivalence used by Huang 2019 to lift an induced-subgraph
max-degree bound on the hypercube to a sensitivity–degree lower bound on
Boolean functions. We state only the direction actually needed by
Huang's Thm 1.4: *hypercube bound ⇒ sensitivity/degree bound*.

This is the corrected form that supersedes `gotsman_linial`. The original
statement was unprovable for `polyDegree f = 0` (constant Boolean
functions), because `hQ` only constrains `h` on `m > 0`, leaving `h 0`
unconstrained. Concrete counter-example to the un-corrected form:
`h(0) = 1/4`, `h(m) = √m` for `m ≥ 1` is monotone and satisfies `hQ`
(matching Huang's bound), but for `f ≡ false` the conclusion `1/4 ≤ 0`
is false.

The fix is the additional hypothesis `(h0 : h 0 ≤ 0)`. Downstream
consumers (e.g. `sensitivity_sq_ge_polyDegree`) supply this trivially
since they take `h = Real.sqrt`, where `h 0 = 0 ≤ 0`.
-/


/-!
# Sketch — `gotsman_linial_with_zero`

Two cases on `polyDegree f`:

* `polyDegree f = 0`: by `h0`, `h 0 ≤ 0 ≤ sensitivity f`.
* `polyDegree f ≥ 1`: Child B (`polyDegree_alternating_sum_witness`)
  gives an `S` of size `polyDegree f` with non-zero Möbius alternating
  sum on `f`. Child C (`bool_func_alternating_sum_sensitivity`)
  then yields `h S.card ≤ sensitivity f`. Substituting
  `S.card = polyDegree f` closes the goal.
-/

theorem solution
    (h : ℕ → ℝ) (hmono : Monotone h) (h0 : h 0 ≤ 0)
    (hQ : ∀ m, 0 < m → ∀ S : Finset (Fin m → Bool), 2 ^ (m - 1) < S.card →
        ∃ v ∈ S, h m ≤ (Hypercube.degreeIn m S v : ℝ))
    {n : ℕ} (f : BoolFunc n) :
    h (polyDegree f) ≤ (sensitivity f : ℝ) := by
  classical
  by_cases hd : polyDegree f = 0
  · -- Constant case: h 0 ≤ 0 ≤ sensitivity f.
    rw [hd]
    have h_sens_nn : (0 : ℝ) ≤ (sensitivity f : ℝ) := Nat.cast_nonneg _
    linarith
  -- polyDegree f ≥ 1.
  have h_pos : 1 ≤ polyDegree f := Nat.one_le_iff_ne_zero.mpr hd
  obtain ⟨S, hS_card, hS_alt⟩ :=
    polyDegree_alternating_sum_witness f h_pos
  have h_S_pos : 1 ≤ S.card := hS_card.symm ▸ h_pos
  have h_bound :=
    bool_func_alternating_sum_sensitivity h hmono hQ f S h_S_pos hS_alt
  rw [hS_card] at h_bound
  exact h_bound
