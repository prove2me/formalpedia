-- Prove2me | Theorems.Thm_BookProof_PermSector_permOp_two_eq_swapH
-- name    : BookProof.PermSector.permOp_two_eq_swapH
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:51:21.083976+00:00
-- url     : https://prove2.me/theorems/0f12c9e3-f582-42dc-a2db-798aa9a0348a
-- title:
--   `BookProof.PermSector.permOp_two_eq_swapH` (x : (Hs.pow 2).carrier) : permOp Hs 2 (Equiv.swap 0 1) x = BookProof.TwoParticleSector.swapH Hs x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.permOp_two_eq_swapH` (x : (Hs.pow 2).carrier) : permOp Hs 2 (Equiv.swap 0 1) x = BookProof.TwoParticleSector.swapH Hs x
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.permOp_two_eq_swapH`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.permOp_two_eq_swapH
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterTensorGraphCore
open BookProof.ChapterGaugeUnconstrainedSpectrum
open BookProof.TensorCore
open BookProof.PermSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.PermSector.permOp_two_eq_swapH (x : (Hs.pow 2).carrier) :
    permOp Hs 2 (Equiv.swap 0 1) x = BookProof.TwoParticleSector.swapH Hs x := by sorry
