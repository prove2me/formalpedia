-- Prove2me | Theorems.Thm_BlockCycleRotation_Eterm_le
-- name    : BlockCycleRotation.Eterm_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:59:08.487798+00:00
-- url     : https://prove2.me/theorems/b7b29362-eb56-4de8-9c2c-c102015284bb
-- title:
--   Every per-divisor error term is $O(n^{3/2})$
-- statement:
--   For $n>0$ and $d \mid n$,
--   $$\mathrm{Eterm}(n,d) \le (8+2C)\, n^{3/2}.$$
--
--   In the bulk case $2d \le m$ the two contributions are $(\sqrt{(m-1)/d}+1)\,dm \le 2n^{3/2}$, using $dm=n$, and $m^2 \cdot 3/(2N) \le 6n^{3/2}$, using the cut-off inequality $\sqrt m \le 4\sqrt d\,N$. In the degenerate case $m < 2d$ one has $m^2 < 2n$ directly. The point of the bound is that it is uniform in $d$, so summing over divisors costs only the divisor function.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 19. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Constant.lean#L656-L741

import Definitions.Def_BlockCycleRotation_Constant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.Eterm_le {n d : ℕ} (hn : 0 < n) (hd : d ∈ n.divisors) :
    Eterm n d ≤ (8 + 2 * cConst) * ((n : ℝ) * Real.sqrt n) := by sorry
