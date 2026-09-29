-- Prove2me | Theorems.Thm_BlockCycleRotation_cConst_le_bulk_add
-- name    : BlockCycleRotation.cConst_le_bulk_add
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:58:18.98559+00:00
-- url     : https://prove2.me/theorems/84e62233-9322-4f17-9c01-863611c54ac2
-- title:
--   Truncating the series for $C$ costs at most $3/(2N)$
-- statement:
--   If every pair $a \le N$, $1 \le a' < a$ satisfies the bulk condition $d\,a(a+a') \le m$, then
--   $$C \le \sum_{a \le N}\sum_{a' < a} \mathbf{1}[\,d\,a(a+a') \le m\,]\,c(a,a') \;+\; \frac{3}{2N}.$$
--
--   The tail of the series for $C$ beyond $a = N$ is controlled by $\sum_{a>N} a^{-2} \le 1/N$ together with the row bound $\sum_{a'<a} c(a,a') \le 5/(8a^2)$. This is the truncation half of Lemma 19.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 19. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Constant.lean#L255-L277

import Definitions.Def_BlockCycleRotation_Constant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.cConst_le_bulk_add {m d N : ℕ} (hN : 0 < N)
    (hbulk : ∀ a a', a ≤ N → 1 ≤ a' → a' < a → d * a * (a + a') ≤ m) :
    cConst ≤ (∑ a ∈ Finset.range (N + 1), ∑ a' ∈ Finset.range a,
        if d * a * (a + a') ≤ m then cTerm (a, a') else 0) + 3 / (2 * (N : ℝ)) := by sorry
