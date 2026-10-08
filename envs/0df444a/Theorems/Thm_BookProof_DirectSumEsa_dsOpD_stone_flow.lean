-- Prove2me | Theorems.Thm_BookProof_DirectSumEsa_dsOpD_stone_flow
-- name    : BookProof.DirectSumEsa.dsOpD_stone_flow
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:00:15.287615+00:00
-- url     : https://prove2.me/theorems/f74b98a3-1771-4a56-8a72-93b5ef5024d8
-- title:
--   `BookProof.DirectSumEsa.dsOpD_stone_flow` [∀ i, CompleteSpace (G i)] (A : ∀ i, D i →ₗ[ℂ] D i) (hdense : ∀ i, Dense ((D i : Submodule ℂ (G i)) : Set (G i))) (hsym : ∀ i, IsSymmetric
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDirectSumEsa`.
--
--   `BookProof.DirectSumEsa.dsOpD_stone_flow` [∀ i, CompleteSpace (G i)] (A : ∀ i, D i →ₗ[ℂ] D i) (hdense : ∀ i, Dense ((D i : Submodule ℂ (G i)) : Set (G i))) (hsym : ∀ i, IsSymmetricDom (A i)) (h : ∀ i, HasZeroDeficiencyOn (D i) (A i)) : ∃ (T : ChapterStoneResolvent.UnboundedSelfAdjoint (lp G 2)) (U : ℝ → (lp G 2 →L[ℂ] lp G 2)), EsaClosure.IsSelfAdjointExtension ((dsCore D).subtype.comp (dsOpD A)) T.op ∧ StoneBridge.IsStoneFlow T U
--
--   Formalization note: Lean 4 identifier `BookProof.DirectSumEsa.dsOpD_stone_flow`.

-- Generated from ChapterDirectSumEsa.lean — theorem BookProof.DirectSumEsa.dsOpD_stone_flow
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
open BookProof.EsaClosure
open BookProof.NavierStokesFlow.FullEsa
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.StoneBridge
open BookProof.DirectSumEsa


open scoped ENNReal


open BookProof.FarisLavine

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

variable {D : ∀ i, Submodule ℂ (G i)}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FullEsa

theorem BookProof.DirectSumEsa.dsOpD_stone_flow [∀ i, CompleteSpace (G i)] (A : ∀ i, D i →ₗ[ℂ] D i)
    (hdense : ∀ i, Dense ((D i : Submodule ℂ (G i)) : Set (G i)))
    (hsym : ∀ i, IsSymmetricDom (A i)) (h : ∀ i, HasZeroDeficiencyOn (D i) (A i)) :
    ∃ (T : ChapterStoneResolvent.UnboundedSelfAdjoint (lp G 2))
      (U : ℝ → (lp G 2 →L[ℂ] lp G 2)),
      EsaClosure.IsSelfAdjointExtension ((dsCore D).subtype.comp (dsOpD A)) T.op ∧
        StoneBridge.IsStoneFlow T U := by sorry
