-- Prove2me | Theorems.Thm_BlockCycleRotation_cConst_eq_alternative
-- name    : BlockCycleRotation.cConst_eq_alternative
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:00:24.401375+00:00
-- url     : https://prove2.me/theorems/a7676123-256b-4aa9-97fa-76577ffa77f9
-- title:
--   Remark 21: $C = \tfrac12 - S/(2\zeta(3))$
-- statement:
--   The constant of equation (const-c) admits the closed form
--   $$C = \frac{1}{2} - \frac{S}{2\,\zeta(3)},$$
--   where $S$ is the auxiliary series of Remark 21.
--
--   This is the identity of Remark 21. It is what makes $C$ — defined as a double series over coprime pairs — numerically accessible: the coprimality constraint is removed by a Möbius factor, which produces $\zeta(3)$, and the remaining series telescopes.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Remark 21. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Remark21.lean#L676-L682

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Remark21
import Mathlib

open BlockCycleRotation
open Real Finset Filter Topology

theorem BlockCycleRotation.cConst_eq_alternative : cConst = 1 / 2 - sConst / (2 * zeta3) := by sorry
