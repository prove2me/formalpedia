-- Prove2me | Theorems.Thm_BookProof_PermSector_essentiallySelfAdjointOn_fermionic
-- name    : BookProof.PermSector.essentiallySelfAdjointOn_fermionic
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-09T17:54:19.304988+00:00
-- url     : https://prove2.me/theorems/b2320716-53d5-4fc7-988b-c025afa04013
-- title:
--   `BookProof.PermSector.essentiallySelfAdjointOn_fermionic` (n : ℕ) (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ n) (sectorOp Hs D₂ A n)) : EssentiallySelfAdjointOn (redDom (fer
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.essentiallySelfAdjointOn_fermionic` (n : ℕ) (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ n) (sectorOp Hs D₂ A n)) : EssentiallySelfAdjointOn (redDom (fermionicProj Hs n) (sectorDom Hs D₂ n)) (redOp (sectorOp Hs D₂ A n) (isReducingProjection_fermionicProj Hs n) ((signRep Hs n).commutes_avgProj (hD := signRep_mem_sectorDom Hs D₂ n) (signRep_commutes_sectorDom Hs D₂ A n)))
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.essentiallySelfAdjointOn_fermionic`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.essentiallySelfAdjointOn_fermionic
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

theorem BookProof.PermSector.essentiallySelfAdjointOn_fermionic (n : ℕ)
    (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ n) (sectorOp Hs D₂ A n)) :
    EssentiallySelfAdjointOn
      (redDom (fermionicProj Hs n) (sectorDom Hs D₂ n))
      (redOp (sectorOp Hs D₂ A n) (isReducingProjection_fermionicProj Hs n)
        ((signRep Hs n).commutes_avgProj
          (hD := signRep_mem_sectorDom Hs D₂ n)
          (signRep_commutes_sectorDom Hs D₂ A n))) := by sorry
