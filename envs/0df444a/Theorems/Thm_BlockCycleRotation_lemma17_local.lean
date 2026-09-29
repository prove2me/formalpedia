-- Prove2me | Theorems.Thm_BlockCycleRotation_lemma17_local
-- name    : BlockCycleRotation.lemma17_local
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:58:42.683556+00:00
-- url     : https://prove2.me/theorems/cb9a81c4-2347-425b-b4ca-25719947ab96
-- title:
--   Lemma 19 at a single divisor
-- statement:
--   Fix a divisor $d$ of $n$ and put $m = n/d$. For any cut-off $N$ such that every pair $a \le N$ lies in the bulk range,
--   $$\left| \sum_{\substack{(a,a') \text{ coprime} \\ d\,a(a+a') \le m}} \left( \frac{dm}{a+a'} + m^2 c(a,a') \right) - m^2 C \right| \le \left(\sqrt{\tfrac{m-1}{d}}+1\right) d\,m \;+\; \frac{3m^2}{2N}.$$
--
--   The first term on the right is the lower-order part of the main term, the second the error committed by truncating the series for $C$ at $N$. Choosing $N \approx \sqrt{m/(2d)}$ balances them, and both are $O(m^{3/2}\sqrt{d})$.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 19. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Constant.lean#L485-L509

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.lemma17_local {m d N : ℕ} (hm : 0 < m) (hd : 0 < d) (hN : 0 < N)
    (hbulk : ∀ a a', a ≤ N → 1 ≤ a' → a' < a → d * a * (a + a') ≤ m) :
    |(∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m),
          ((d : ℝ) * (m : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ)) + (m : ℝ) ^ 2 * cTerm p))
        - (m : ℝ) ^ 2 * cConst|
      ≤ ((Nat.sqrt ((m - 1) / d) : ℝ) + 1) * ((d : ℝ) * (m : ℝ))
        + (m : ℝ) ^ 2 * (3 / (2 * (N : ℝ))) := by sorry
