-- Prove2me | Theorems.Thm_BlockCycleRotation_bulk_double_le_pairs
-- name    : BlockCycleRotation.bulk_double_le_pairs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:58:55.057904+00:00
-- url     : https://prove2.me/theorems/5d290f35-1ad2-4ee2-9cac-15e7e94bcf7d
-- title:
--   Index reconciliation between the truncated series and the bulk pairs
-- statement:
--   For $d>0$ and any $N$,
--   $$\sum_{a \le N} \sum_{a' < a} \mathbf{1}[\,d\,a(a+a') \le m\,]\; c(a,a') \le \sum_{\substack{(a,a') \text{ coprime} \\ d\,a(a+a') \le m}} c(a,a').$$
--
--   The series defining $C$ is indexed by all pairs $a' < a$, the main term by *coprime* pairs in the bulk range. This inequality reconciles the two index sets, which is what allows the truncation bound for $C$ to be compared term by term with the sum actually appearing in the main term.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 19. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Constant.lean#L365-L418

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.bulk_double_le_pairs {m d N : ℕ} (hd : 0 < d) :
    ∑ a ∈ Finset.range (N + 1), ∑ a' ∈ Finset.range a,
        (if d * a * (a + a') ≤ m then cTerm (a, a') else 0)
      ≤ ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m), cTerm p := by sorry
