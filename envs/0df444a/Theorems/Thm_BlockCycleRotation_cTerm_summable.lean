-- Prove2me | Theorems.Thm_BlockCycleRotation_cTerm_summable
-- name    : BlockCycleRotation.cTerm_summable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:57:56.657023+00:00
-- url     : https://prove2.me/theorems/ccd828ec-b982-45ab-a58c-ee53c5878b0d
-- title:
--   The series for `C` converges
-- statement:
--   **The series for `C` converges.**
--
--   In Blomer–Bux this is **Eq. (const-c)**, “Convergence of the series for `C`”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Eq. (const-c). Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Constant.lean#L86-L98

import Definitions.Def_BlockCycleRotation_Constant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.cTerm_summable : Summable cTerm := by sorry
