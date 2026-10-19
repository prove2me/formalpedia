-- Prove2me | Theorems.Thm_BookProof_PermSector_signRep_commutes_sectorDom
-- name    : BookProof.PermSector.signRep_commutes_sectorDom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:45:11.4854+00:00
-- url     : https://prove2.me/theorems/7a735037-b0cd-4320-bac4-f59e56d0ec9f
-- title:
--   `BookProof.PermSector.signRep_commutes_sectorDom` (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : sectorDom Hs D₂ n) : sectorOp Hs D₂ A n ⟨(signRep Hs n).act σ (x : (Hs.pow n).carrier), sign
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.signRep_commutes_sectorDom` (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : sectorDom Hs D₂ n) : sectorOp Hs D₂ A n ⟨(signRep Hs n).act σ (x : (Hs.pow n).carrier), signRep_mem_sectorDom Hs D₂ n σ _ x.2⟩ = (signRep Hs n).act σ (sectorOp Hs D₂ A n x)
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.signRep_commutes_sectorDom`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.signRep_commutes_sectorDom
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterWignerLittleGroup
import Theorems.Thm_BookProof_PermSector_signRep_mem_sectorDom
open BookProof.ChapterGaugeUnconstrainedSpectrum
open BookProof.TensorCore
open BookProof.ChapterWignerLittleGroup
open BookProof.PermSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.PermSector.signRep_commutes_sectorDom (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : sectorDom Hs D₂ n) :
    sectorOp Hs D₂ A n ⟨(signRep Hs n).act σ (x : (Hs.pow n).carrier),
        signRep_mem_sectorDom Hs D₂ n σ _ x.2⟩
      = (signRep Hs n).act σ (sectorOp Hs D₂ A n x) := by sorry
