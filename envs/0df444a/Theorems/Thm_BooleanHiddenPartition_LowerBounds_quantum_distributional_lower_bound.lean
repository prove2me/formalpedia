-- Prove2me | Theorems.Thm_BooleanHiddenPartition_LowerBounds_quantum_distributional_lower_bound
-- name    : BooleanHiddenPartition.LowerBounds.quantum_distributional_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:23:05.089531+00:00
-- url     : https://prove2.me/theorems/2a986b7b-a9ac-439c-81e4-f039fa623097
-- title:
--   Theorem 10 — Quantum hard-distribution lower bound
-- statement:
--   Fix k>0, a Boolean predicate f, and alpha in (0,1). There is D>0 depending only on f and alpha, uniformly in every 1≤d≤k, every mass q with the prescribed zero correlations, admissible input lengths, encoders, measurements and random seeds. For any unassisted c-qubit one-way protocol under the hard distribution and every epsilon>0,
--
--   $$c<\epsilon^{2/d}n^{1-2/d}/D\quad\Longrightarrow\quad\Pr[\mathrm{correct}]\leq\tfrac12+\epsilon.$$
--
--   All mixed message states, two-outcome POVMs and measurable public randomness are included. The strict threshold and its full constants, powers and alpha range are unchanged. This is the quantitative quantum bound supporting Result 1.
--
--   Differences from the source:
--   - encoding: Coordinates in {+1,−1} indexed from 1 → Fin-indexed Bool coordinates with true=−1, and explicit finite averages; reason: The sign map is a bijection and preserves ordered blocks, parities, distributions and all source instances.
--   - encoding: Positive source parameters with alpha n/k an integer → A positive integer m and Layout with k*m=alpha*n; reason: This is the same admissibility condition without truncating division; irrational alpha retains the source admissibility quantifier.
--   - encoding: An O-bound with the dependencies specified in the text → A positive existential constant before every varying datum; reason: This spells out the source uniformity without choosing a numeral or weakening a power.
--   - encoding: The displayed 1/d and 2/d → The defined domain d>0; reason: The printed expressions have no ordinary value at d=0; all cases with defined exponents are retained.
--   - encoding: Density matrices and the Schatten 1-norm → Referenced PSD trace-one matrices and Re Tr sqrt(A-adjoint*A); reason: This includes every mixed state and uses the unhalved norm of the source.
--   - encoding: Arbitrary unassisted quantum one-way protocols → Density encoders, POVM effects and a measurable probability-space public seed; reason: These describe all mixed messages and binary measurements; their bounded Born probabilities are integrable, with no shared entangled register.
-- source:
--   Mark Bun, Joao F. Doriguello, John Kallaugher, Nadezhda Voronova, STOC 2027 submission #1085 (October 2026), p. 22, Theorem 10.

import Definitions.Def_BooleanHiddenPartition_LowerBounds_Posteriors

open scoped BigOperators ENNReal
open Classical
set_option autoImplicit false

namespace BooleanHiddenPartition.LowerBounds

noncomputable section

/-- Theorem 10, p.22; arbitrary mixed messages, POVMs and public random seeds. -/
theorem quantum_distributional_lower_bound (k : ℕ) (hk : 0 < k)
    (f : Cube k → Bool) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ (d : ℕ), 0 < d → d ≤ k →
      ∀ (q : Cube k → ℝ), IsMass q → moments f q d →
      ∀ (n m c : ℕ) (L : Layout k n m α) (ε : ℝ), 0 < ε →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : QuantumProtocol (Cube n) (BobInput n m) Ω c),
        (c : ℝ) < ε ^ (2 / (d : ℝ)) * (n : ℝ) ^ (1 - 2 / (d : ℝ)) / D →
        hardSuccess L f q (randomizedQuantumAccept P) ≤ 1 / 2 + ε := by sorry

end

end BooleanHiddenPartition.LowerBounds
