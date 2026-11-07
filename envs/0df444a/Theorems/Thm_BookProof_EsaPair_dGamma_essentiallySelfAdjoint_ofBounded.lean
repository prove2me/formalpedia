-- Prove2me | Theorems.Thm_BookProof_EsaPair_dGamma_essentiallySelfAdjoint_ofBounded
-- name    : BookProof.EsaPair.dGamma_essentiallySelfAdjoint_ofBounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:52:47.541914+00:00
-- url     : https://prove2.me/theorems/eeea1bbb-6f1d-4c1e-8e31-e334a2f0cfac
-- title:
--   `BookProof.EsaPair.dGamma_essentiallySelfAdjoint_ofBounded` (Hs : IPSpace) (B : (⊤ : Submodule ℂ Hs.carrier) →ₗ[ℂ] Hs.carrier) (hB : SymmetricOn ⊤ B) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEsaPairDGamma`.
--
--   `BookProof.EsaPair.dGamma_essentiallySelfAdjoint_ofBounded` (Hs : IPSpace) (B : (⊤ : Submodule ℂ Hs.carrier) →ₗ[ℂ] Hs.carrier) (hB : SymmetricOn ⊤ B) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ a : (⊤ : Submodule ℂ Hs.carrier), ‖B a‖ ≤ C * ‖(a : Hs.carrier)‖) (D : Submodule ℂ Hs.carrier) (hdense : Dense (D : Set Hs.carrier)) : EssentiallySelfAdjointOn (dsCore (fun n : ℕ => fockSectorCore Hs ⊤ D n)) (dGammaCoreOp Hs ⊤ B D)
--
--   Formalization note: Lean 4 identifier `BookProof.EsaPair.dGamma_essentiallySelfAdjoint_ofBounded`.

-- Generated from ChapterEsaPairDGamma.lean — theorem BookProof.EsaPair.dGamma_essentiallySelfAdjoint_ofBounded
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterEsaPairDGamma
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterSirkTrotterKatoGalerkin
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.DirectSumEsa
open BookProof.TensorCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.EsaPair
open BookProof.SecondQuantizationCore

noncomputable section

variable {Hs : IPSpace} (P : ESAPair Hs)

theorem BookProof.EsaPair.dGamma_essentiallySelfAdjoint_ofBounded (Hs : IPSpace)
    (B : (⊤ : Submodule ℂ Hs.carrier) →ₗ[ℂ] Hs.carrier) (hB : SymmetricOn ⊤ B) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ a : (⊤ : Submodule ℂ Hs.carrier), ‖B a‖ ≤ C * ‖(a : Hs.carrier)‖)
    (D : Submodule ℂ Hs.carrier) (hdense : Dense (D : Set Hs.carrier)) :
    EssentiallySelfAdjointOn (dsCore (fun n : ℕ => fockSectorCore Hs ⊤ D n))
      (dGammaCoreOp Hs ⊤ B D) := by sorry
