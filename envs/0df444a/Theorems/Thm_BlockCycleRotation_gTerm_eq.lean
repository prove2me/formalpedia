-- Prove2me | Theorems.Thm_BlockCycleRotation_gTerm_eq
-- name    : BlockCycleRotation.gTerm_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:59:38.113493+00:00
-- url     : https://prove2.me/theorems/9aeae19e-d691-4eff-aa5f-e4e1da24bb7d
-- title:
--   Step 1 of Remark 21
-- statement:
--   **Step 1 of Remark 21.** `(2a+a')/(2a²(a+a')²) = (1/(2a'))(1/a² - 1/(a+a')²)`.
--
--   In Blomer–Bux this is **Remark 21**, “Summand rewriting”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Remark 21. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Remark21.lean#L62-L76

import Definitions.Def_BlockCycleRotation_Remark21
import Mathlib

open BlockCycleRotation
open Real Finset Filter Topology

theorem BlockCycleRotation.gTerm_eq (p : ℕ × ℕ) : gTerm p = (zTerm p - eTerm p) / 2 := by sorry
