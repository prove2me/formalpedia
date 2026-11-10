-- Prove2me | Theorems.Thm_BooleanHiddenPartition_LowerBounds_classical_distributional_lower_bound
-- name    : BooleanHiddenPartition.LowerBounds.classical_distributional_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:22:58.613201+00:00
-- url     : https://prove2.me/theorems/c5dea3f2-df94-4dd7-922f-3ac93ad3b424
-- title:
--   Theorem 7 — Classical hard-distribution lower bound
-- statement:
--   Fix k>0, a Boolean predicate f, and alpha in (0,1). There is D>0 depending only on f and alpha, uniformly for every 1≤d≤k, every mass q with zero correlations below d, every admissible n and every randomized c-bit one-way protocol. Under the correlated hard input distribution, for every epsilon>0,
--
--   $$c<\epsilon^{2/d}n^{1-1/d}/D\quad\Longrightarrow\quad\Pr[\mathrm{correct}]\leq\tfrac12+\epsilon.$$
--
--   The strict threshold, exact power 2/d and full range of alpha are retained. The protocol may use arbitrary public and private randomness; q may vanish on cube points. This is the quantitative distributional classical bound supporting Result 1.
--
--   Differences from the source:
--   - encoding: Coordinates in {+1,−1} indexed from 1 → Fin-indexed Bool coordinates with true=−1, and explicit finite averages; reason: The sign map is a bijection and preserves ordered blocks, parities, distributions and all source instances.
--   - encoding: Positive source parameters with alpha n/k an integer → A positive integer m and Layout with k*m=alpha*n; reason: This is the same admissibility condition without truncating division; irrational alpha retains the source admissibility quantifier.
--   - encoding: An O-bound with the dependencies specified in the text → A positive existential constant before every varying datum; reason: This spells out the source uniformity without choosing a numeral or weakening a power.
--   - encoding: The displayed 1/d and 2/d → The defined domain d>0; reason: The printed expressions have no ordinary value at d=0; all cases with defined exponents are retained.
--   - encoding: Alice sends an arbitrary randomized classical c-bit message → A probability law on deterministic encoder/decoder tables with 2^c symbols; reason: Finite inputs permit fixing all coins to tables, and padding gives the same worst-case cost and all randomized protocols.
-- source:
--   Mark Bun, Joao F. Doriguello, John Kallaugher, Nadezhda Voronova, STOC 2027 submission #1085 (October 2026), p. 15, Theorem 7.

import Definitions.Def_BooleanHiddenPartition_LowerBounds_Posteriors

open scoped BigOperators ENNReal
open Classical
set_option autoImplicit false

namespace BooleanHiddenPartition.LowerBounds

noncomputable section

/-- Theorem 7, p.15. Positive d is the domain of the printed 1/d and 2/d. -/
theorem classical_distributional_lower_bound (k : ℕ) (hk : 0 < k)
    (f : Cube k → Bool) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ (d : ℕ), 0 < d → d ≤ k →
      ∀ (q : Cube k → ℝ), IsMass q → moments f q d →
      ∀ (n m c : ℕ) (L : Layout k n m α) (ε : ℝ), 0 < ε →
      ∀ P : ClassicalProtocol (Cube n) (BobInput n m) c,
        (c : ℝ) < ε ^ (2 / (d : ℝ)) * (n : ℝ) ^ (1 - 1 / (d : ℝ)) / D →
        hardSuccess L f q (classicalAccept P) ≤ 1 / 2 + ε := by sorry

end

end BooleanHiddenPartition.LowerBounds
