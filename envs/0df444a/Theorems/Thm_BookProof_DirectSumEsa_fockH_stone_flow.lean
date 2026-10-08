-- Prove2me | Theorems.Thm_BookProof_DirectSumEsa_fockH_stone_flow
-- name    : BookProof.DirectSumEsa.fockH_stone_flow
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:00:50.016348+00:00
-- url     : https://prove2.me/theorems/0d07acdf-9a30-4029-8115-bea65d10fbbb
-- title:
--   `BookProof.DirectSumEsa.fockH_stone_flow` {w : ℝ → ℝ} (hw : Measurable w) : ∃ (T : ChapterStoneResolvent.UnboundedSelfAdjoint fockSpace) (U : ℝ → (fockSpace →L[ℂ] fockSpace)), EsaC
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDirectSumEsa`.
--
--   `BookProof.DirectSumEsa.fockH_stone_flow` {w : ℝ → ℝ} (hw : Measurable w) : ∃ (T : ChapterStoneResolvent.UnboundedSelfAdjoint fockSpace) (U : ℝ → (fockSpace →L[ℂ] fockSpace)), EsaClosure.IsSelfAdjointExtension ((fockCore w).subtype.comp (fockH hw)) T.op ∧ StoneBridge.IsStoneFlow T U
--
--   Formalization note: Lean 4 identifier `BookProof.DirectSumEsa.fockH_stone_flow`.

-- Generated from ChapterDirectSumEsa.lean — theorem BookProof.DirectSumEsa.fockH_stone_flow
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
open BookProof.EsaClosure
open BookProof.ChapterLinftyMultiplication
open BookProof.NavierStokesFlow.FockContinuum
open BookProof.StoneBridge
open BookProof.DirectSumEsa


open scoped ENNReal


open BookProof.FarisLavine

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

variable {D : ∀ i, Submodule ℂ (G i)}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.DirectSumEsa.fockH_stone_flow {w : ℝ → ℝ} (hw : Measurable w) :
    ∃ (T : ChapterStoneResolvent.UnboundedSelfAdjoint fockSpace)
      (U : ℝ → (fockSpace →L[ℂ] fockSpace)),
      EsaClosure.IsSelfAdjointExtension ((fockCore w).subtype.comp (fockH hw)) T.op ∧
        StoneBridge.IsStoneFlow T U := by sorry
