-- Prove2me | Theorems.Thm_BlockCycleRotation_lemma17
-- name    : BlockCycleRotation.lemma17
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:58:53.755675+00:00
-- url     : https://prove2.me/theorems/6ffa7fd9-3b3f-434d-9ad9-0e12eba1adf0
-- title:
--   Lemma 19: the main term, with the per-divisor errors abstracted
-- statement:
--   Let $E(d)$ bound, for each divisor $d \mid n$, the deviation of the bulk main term at $d$ from $(n/d)^2 C$. Then
--   $$\left| G_1(n) - C\,n^2 \sum_{d\mid n} \frac{1}{d^2} \right| \le \sum_{d \mid n} E(d).$$
--
--   This is Lemma 19 stated with its error term as a hypothesis, so that the combinatorial reduction and the numerical estimation of the error are separated. The instantiation of $E$ is `Eterm`, bounded by $(8+2C)n^{3/2}$ per divisor.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 19. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Constant.lean#L521-L549

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.lemma17 {n : ℕ} (hn : 0 < n) (E : ℕ → ℝ)
    (hE : ∀ d ∈ n.divisors,
      |(∑ p ∈ (coprimePairs (n / d)).filter (fun p => d * p.1 * (p.1 + p.2) ≤ n / d),
            ((d : ℝ) * ((n / d : ℕ) : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ))
              + ((n / d : ℕ) : ℝ) ^ 2 * cTerm p))
          - ((n / d : ℕ) : ℝ) ^ 2 * cConst| ≤ E d) :
    |G1 n - cConst * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2|
      ≤ ∑ d ∈ n.divisors, E d := by sorry
