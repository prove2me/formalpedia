-- Prove2me | Theorems.Thm_BookProof_PermSector_symmetricOn_fermionic
-- name    : BookProof.PermSector.symmetricOn_fermionic
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-09T17:54:24.212433+00:00
-- url     : https://prove2.me/theorems/1fab9082-3c36-4673-86ac-5a7ea3014a5c
-- title:
--   `BookProof.PermSector.symmetricOn_fermionic` (n : ℕ) (hA : SymmetricOn D₂ A) : SymmetricOn (redDom (fermionicProj Hs n) (sectorDom Hs D₂ n)) (redOp (sectorOp Hs D₂ A n) (isReducing
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.symmetricOn_fermionic` (n : ℕ) (hA : SymmetricOn D₂ A) : SymmetricOn (redDom (fermionicProj Hs n) (sectorDom Hs D₂ n)) (redOp (sectorOp Hs D₂ A n) (isReducingProjection_fermionicProj Hs n) ((signRep Hs n).commutes_avgProj (hD := signRep_mem_sectorDom Hs D₂ n) (signRep_commutes_sectorDom Hs D₂ A n)))
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.symmetricOn_fermionic`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.symmetricOn_fermionic
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_PermSector_isReducingProjection_fermionicProj
import Theorems.Thm_BookProof_PermSector_permRep_mem_sectorDom
import Theorems.Thm_BookProof_PermSector_permRep_commutes_sectorDom
import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_commutes_avgProj
import Theorems.Thm_BookProof_PermSector_signRep_mem_sectorDom
import Theorems.Thm_BookProof_PermSector_signRep_commutes_sectorDom
open BookProof.ChapterGaugeUnconstrainedSpectrum
open BookProof.TensorCore
open BookProof.PermSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.PermSector.symmetricOn_fermionic (n : ℕ) (hA : SymmetricOn D₂ A) :
    SymmetricOn (redDom (fermionicProj Hs n) (sectorDom Hs D₂ n))
      (redOp (sectorOp Hs D₂ A n) (isReducingProjection_fermionicProj Hs n)
        ((signRep Hs n).commutes_avgProj
          (hD := signRep_mem_sectorDom Hs D₂ n)
          (signRep_commutes_sectorDom Hs D₂ A n))) := by sorry
