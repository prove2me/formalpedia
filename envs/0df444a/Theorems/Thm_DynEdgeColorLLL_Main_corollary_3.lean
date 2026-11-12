-- Prove2me | Theorems.Thm_DynEdgeColorLLL_Main_corollary_3
-- name    : DynEdgeColorLLL.Main.corollary_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:21.601063+00:00
-- url     : https://prove2.me/theorems/5a752558-cfd2-4a57-9f27-ebab502a77e4
-- title:
--   Corollary 3 — $\mathbb E|Z_r|=O(s^2q^r|B|)$ and expected recourse $O(s^2q|B|)$
-- statement:
--   Let a batch $B$ of distinct clause updates turn $\mathrm{vbl}^{old}$ into $\mathrm{vbl}^{new}$. Suppose both instances satisfy the standing assumptions of §3.1 with the same $k,s,d,q,K$ (each with its own function $x$ in assumption (1)), and run both static transcripts on the same randomness tables. Let $Z_r=\{x:b^{old}_{x,r}\ne b^{new}_{x,r}\}$. Then there is an absolute constant $C$ such that for every $r\ge1$
--   $$\mathbb E\bigl[|Z_r|\bigr]\le C\,K\,s^2q^r|B| ,$$
--   and the expected recourse, the expected number of variables $x$ with $\sigma^{old}_\infty(x)\ne\sigma^{new}_\infty(x)$, is at most $C\,K\,s^2q|B|$.
--
--   Together with the stage-by-stage repair this gives the recourse bound of Theorem 2, the dynamic LLL. The theorems on edge colouring use that bound.
--
--   **Formalization Note.** The expected size of a random set of variables is written as the sum over variables of the probability of membership (linearity of expectation).
--
--   Differences from the source:
--   - reading: O(s²q^r|B|) and O(s²q|B|) → C·K·s²q^r|B| and C·K·s²q|B| with C absolute; reason: the O hides only the constant of assumption (1)'s max x/(1−x) = O(1)
--   - generalization: the convention "we may take k ≤ d" (PDF p. 11) → k ≤ d is not assumed; reason: the bound then holds a fortiori for k ≤ d
--   - encoding: a set V of variables and clause IDs in [m] → a finite type of variables and clause IDs Fin m; reason: every instance in the paper is finite at every moment
--   - encoding: E[|Z_r|] and the expected number of changed output values → the sum over variables of the (outer) probability of membership; reason: linearity of expectation; equal for measurable events and an upper bound otherwise
--   - encoding: σ_∞(x) = R(x, s_x) → R(x, s_x) with the junk entry R(x, 0) when s_x = ∞; reason: this changes the integrand only on an event of probability zero (the algorithm terminates almost surely, PDF p. 13)
--   - encoding: a truth table f_{C,U} : ∏_{x∈U} Ω_x → {0,1} for each clause C and variable set U → a predicate f C U on full assignments that depends only on the coordinates in U, is false for U = ∅, and has a measurable falsifying set (IsTruthTableFamily); reason: the same truth tables; the empty-clause convention is stated in §3.1, and measurability is presupposed by Pr[C] in assumption (1)
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), Corollary 3, printed p. 12 (PDF p. 14); standing assumptions §3.1, printed pp. 9–10 (PDF pp. 11–12)

import Mathlib
import Definitions.Def_DynEdgeColorLLL_Main_LLLTranscript
open MeasureTheory
open scoped ENNReal

namespace DynEdgeColorLLL.Main

open Classical in
/-- Corollary 3 (Peng–Ghaffari, STOC 2027 submission #615, printed p. 12, PDF p. 14). Let the new
instance arise from the old one by a batch `B` of distinct clause updates, both satisfying the
standing assumptions of §3.1 with the same `k, s, d, q, K`, and run both transcripts on the same
randomness tables. With `Z_r = {x : b^old_{x,r} ≠ b^new_{x,r}}`, for every `r ≥ 1`,
`E[|Z_r|] = O(s² q^r |B|)`; consequently the expected recourse, the number of variables whose
final value `σ_∞` changes, is `O(s² q |B|)`. Expectations of counts are written as sums of
probabilities (linearity of expectation); the `O` hides an absolute constant times `K`. -/
theorem corollary_3 :
    ∃ Cabs : ℝ, ∀ {X : Type} [Fintype X] [DecidableEq X] {Ω : X → Type}
      [∀ x, MeasurableSpace (Ω x)] (D : (x : X) → Measure (Ω x))
      [∀ x, IsProbabilityMeasure (D x)] {m : ℕ} (f : TruthTables X Ω m)
      (vbl : Fin m → Finset X) (B : Finset (Fin m × X)) (k s d : ℕ) (q K : ℝ)
      (xw xw' : Fin m → ℝ),
      IsTruthTableFamily f → HasParams vbl k s d → HasParams (applyBatch vbl B) k s d →
      (0 < q ∧ q < 1 / 2) → Assumption1 D f vbl d q K xw →
      Assumption1 D f (applyBatch vbl B) d q K xw' →
      (∀ r : ℕ, 1 ≤ r →
        ∑ x : X, tableMeasure D
            {τ | ¬ (bx f vbl τ x r ↔ bx f (applyBatch vbl B) τ x r)} ≤
          ENNReal.ofReal (Cabs * K * (s : ℝ) ^ 2 * q ^ r * B.card)) ∧
      ∑ x : X, tableMeasure D
          {τ | finalAssign f vbl τ x ≠ finalAssign f (applyBatch vbl B) τ x} ≤
        ENNReal.ofReal (Cabs * K * (s : ℝ) ^ 2 * q * B.card) := by sorry

end DynEdgeColorLLL.Main
