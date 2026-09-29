-- Prove2me | Theorems.Thm_BlockCycleRotation_gTerm_smul
-- name    : BlockCycleRotation.gTerm_smul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:59:52.731951+00:00
-- url     : https://prove2.me/theorems/c431b464-6e14-4690-a832-1c7214525415
-- title:
--   `gTerm` is homogeneous of degree `-3`
-- statement:
--   **`gTerm` is homogeneous of degree `-3`.**
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `tsum_gTerm_eq`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Remark21.lean#L223-L240

import Definitions.Def_BlockCycleRotation_Remark21
import Mathlib

open BlockCycleRotation
open Real Finset Filter Topology

theorem BlockCycleRotation.gTerm_smul {k a a' : ℕ} (hk : 0 < k) (h1 : 1 ≤ a') (h2 : a' < a) :
    gTerm (k * a, k * a') = gTerm (a, a') / (k : ℝ) ^ 3 := by sorry
