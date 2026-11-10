-- Prove2me | Theorems.Thm_BookProof_PermSector_essentiallySelfAdjointOn_bosonic_core
-- name    : BookProof.PermSector.essentiallySelfAdjointOn_bosonic_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-09T17:24:11.464195+00:00
-- url     : https://prove2.me/theorems/2254caf9-72f9-4565-bbe4-5bcb75cac01d
-- title:
--   `BookProof.PermSector.essentiallySelfAdjointOn_bosonic_core` (n : ℕ) (hcore : IsGraphCore D A) (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ n) (sectorOp Hs D₂ A n)) : Essentia
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.essentiallySelfAdjointOn_bosonic_core` (n : ℕ) (hcore : IsGraphCore D A) (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ n) (sectorOp Hs D₂ A n)) : EssentiallySelfAdjointOn (redDom (bosonicProj Hs n) (sectorCore Hs D₂ D n)) (redOp (restrictOp (sectorOp Hs D₂ A n) (sectorCore_le_sectorDom Hs D₂ D n)) (isReducingProjection_bosonicProj Hs n) ((permRep Hs n).commutes_avgProj (hD := permRep_mem_sectorCore Hs D₂ D n) (permRep_commutes_sectorCore Hs D₂ A D n)))
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.essentiallySelfAdjointOn_bosonic_core`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.essentiallySelfAdjointOn_bosonic_core
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_PermSector_isReducingProjection_bosonicProj
import Theorems.Thm_BookProof_PermSector_permRep_mem_sectorCore
import Theorems.Thm_BookProof_PermSector_permRep_commutes_sectorCore
import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_commutes_avgProj
open BookProof.DirectSumEsa
open BookProof.GraphCore
open BookProof.TensorCore
open BookProof.PermSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.PermSector.essentiallySelfAdjointOn_bosonic_core (n : ℕ) (hcore : IsGraphCore D A)
    (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ n) (sectorOp Hs D₂ A n)) :
    EssentiallySelfAdjointOn
      (redDom (bosonicProj Hs n) (sectorCore Hs D₂ D n))
      (redOp (restrictOp (sectorOp Hs D₂ A n) (sectorCore_le_sectorDom Hs D₂ D n))
        (isReducingProjection_bosonicProj Hs n)
        ((permRep Hs n).commutes_avgProj
          (hD := permRep_mem_sectorCore Hs D₂ D n)
          (permRep_commutes_sectorCore Hs D₂ A D n))) := by sorry
