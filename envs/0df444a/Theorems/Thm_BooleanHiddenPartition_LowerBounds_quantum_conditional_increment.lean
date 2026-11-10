-- Prove2me | Theorems.Thm_BooleanHiddenPartition_LowerBounds_quantum_conditional_increment
-- name    : BooleanHiddenPartition.LowerBounds.quantum_conditional_increment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:23:03.936797+00:00
-- url     : https://prove2.me/theorems/b4ea7ce0-5667-41fc-a23e-0051cc56dcbf
-- title:
--   Lemma 11 — Conditional density-matrix trace-norm increment
-- statement:
--   Fix k>0 and alpha in (0,1). There is K>0 depending only on k and alpha. For all 1≤d≤k, Boolean f, masses q with zero correlations below d, admissible layouts, and arbitrary c-qubit density encoders g, let m_sigma,z be the computed conditional average of g under Q_sigma given the block-output prefix z. For every block i,
--
--   $$\mathbb E_{\sigma,y}[\|m_{\sigma,y_{\leq i}}-m_{\sigma,y_{\leq i-1}}\|_1]\leq K(c/n)^{d/2}.$$
--
--   The expectation is over the actual hard-law marginal of sigma and y, including its independent hidden bit. No half factor is inserted in the trace norm. The statement includes c=0 and all large costs, as well as the range used in the proof.
--
--   Differences from the source:
--   - encoding: Coordinates in {+1,−1} indexed from 1 → Fin-indexed Bool coordinates with true=−1, and explicit finite averages; reason: The sign map is a bijection and preserves ordered blocks, parities, distributions and all source instances.
--   - encoding: Positive source parameters with alpha n/k an integer → A positive integer m and Layout with k*m=alpha*n; reason: This is the same admissibility condition without truncating division; irrational alpha retains the source admissibility quantifier.
--   - encoding: An O-bound with the dependencies specified in the text → A positive existential constant before every varying datum; reason: This spells out the source uniformity without choosing a numeral or weakening a power.
--   - encoding: The displayed 1/d and 2/d → The defined domain d>0; reason: The printed expressions have no ordinary value at d=0; all cases with defined exponents are retained.
--   - encoding: Density matrices and the Schatten 1-norm → Referenced PSD trace-one matrices and Re Tr sqrt(A-adjoint*A); reason: This includes every mixed state and uses the unhalved norm of the source.
--   - encoding: Conditional distributions and states under the hard law → Explicit normalized masses and entrywise matrix averages, zero on null events; reason: These are the actual constructed source objects; null events contribute zero to the expectations.
-- source:
--   Mark Bun, Joao F. Doriguello, John Kallaugher, Nadezhda Voronova, STOC 2027 submission #1085 (October 2026), p. 23, Lemma 11.

import Definitions.Def_BooleanHiddenPartition_LowerBounds_Posteriors

open scoped BigOperators ENNReal
open Classical
set_option autoImplicit false

namespace BooleanHiddenPartition.LowerBounds

noncomputable section

/-- Lemma 11, p.23, including the no-message case discussed on p.22. -/
theorem quantum_conditional_increment (k : ℕ) (hk : 0 < k) (α : ℝ)
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (d : ℕ), 0 < d → d ≤ k →
      ∀ (f : Cube k → Bool) (q : Cube k → ℝ), IsMass q → moments f q d →
      ∀ (n m c : ℕ) (L : Layout k n m α) (g : Cube n → QMat c),
      (∀ x, WildeQIT.IsDensityOperator (g x)) → ∀ i : Fin m,
        quantumIncrement L f q g i ≤ K * ((c : ℝ) / n) ^ ((d : ℝ) / 2) := by sorry

end

end BooleanHiddenPartition.LowerBounds
