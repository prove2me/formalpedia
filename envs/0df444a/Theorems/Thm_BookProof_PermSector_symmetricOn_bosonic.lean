-- Prove2me | Theorems.Thm_BookProof_PermSector_symmetricOn_bosonic
-- name    : BookProof.PermSector.symmetricOn_bosonic
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-09T17:24:35.755429+00:00
-- url     : https://prove2.me/theorems/feda017d-e8dc-4718-bad1-0bf88449b571
-- title:
--   `BookProof.PermSector.symmetricOn_bosonic` (n : ℕ) (hA : SymmetricOn D₂ A) : SymmetricOn (redDom (bosonicProj Hs n) (sectorDom Hs D₂ n)) (redOp (sectorOp Hs D₂ A n) (isReducingProj
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.symmetricOn_bosonic` (n : ℕ) (hA : SymmetricOn D₂ A) : SymmetricOn (redDom (bosonicProj Hs n) (sectorDom Hs D₂ n)) (redOp (sectorOp Hs D₂ A n) (isReducingProjection_bosonicProj Hs n) ((permRep Hs n).commutes_avgProj (hD := permRep_mem_sectorDom Hs D₂ n) (permRep_commutes_sectorDom Hs D₂ A n)))
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.symmetricOn_bosonic`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.symmetricOn_bosonic
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_PermSector_isReducingProjection_bosonicProj
import Theorems.Thm_BookProof_PermSector_permRep_mem_sectorDom
import Theorems.Thm_BookProof_PermSector_permRep_commutes_sectorDom
import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_commutes_avgProj
open BookProof.TensorCore
open BookProof.PermSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.PermSector.symmetricOn_bosonic (n : ℕ) (hA : SymmetricOn D₂ A) :
    SymmetricOn (redDom (bosonicProj Hs n) (sectorDom Hs D₂ n))
      (redOp (sectorOp Hs D₂ A n) (isReducingProjection_bosonicProj Hs n)
        ((permRep Hs n).commutes_avgProj
          (hD := permRep_mem_sectorDom Hs D₂ n)
          (permRep_commutes_sectorDom Hs D₂ A n))) := by sorry
