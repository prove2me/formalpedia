-- Prove2me | Theorems.Thm_BlockCycleRotation_cConst_ge
-- name    : BlockCycleRotation.cConst_ge
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:01:18.099322+00:00
-- url     : https://prove2.me/theorems/de655a79-d0e0-44fc-9f2f-d48c6f1fe9f2
-- title:
--   `C ≥ 0.2025`
-- statement:
--   **`C ≥ 0.2025`.**
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Numeric.lean#L438-L456

import Definitions.Def_BlockCycleRotation_Constant
import Mathlib

open BlockCycleRotation
open Real Finset Filter Topology

theorem BlockCycleRotation.cConst_ge : (2025 : ℝ) / 10000 ≤ cConst := by sorry
