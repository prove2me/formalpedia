-- Prove2me | Theorems.Thm_BookProof_SecondQuantizationCore_dGamma_essentiallySelfAdjointOn_fockCore
-- name    : BookProof.SecondQuantizationCore.dGamma_essentiallySelfAdjointOn_fockCore
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:50:59.528839+00:00
-- url     : https://prove2.me/theorems/75020267-bee2-4fe0-8d75-23c0d6eb5c8a
-- title:
--   `BookProof.SecondQuantizationCore.dGamma_essentiallySelfAdjointOn_fockCore` (hcore : IsGraphCore D A) (hsector : ∀ n : ℕ, EssentiallySelfAdjointOn (fockSectorDom Hs D₂ n) (fockSect
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSecondQuantizationCoreEsa`.
--
--   `BookProof.SecondQuantizationCore.dGamma_essentiallySelfAdjointOn_fockCore` (hcore : IsGraphCore D A) (hsector : ∀ n : ℕ, EssentiallySelfAdjointOn (fockSectorDom Hs D₂ n) (fockSectorOp Hs D₂ A n)) : EssentiallySelfAdjointOn (dsCore (fun n : ℕ => fockSectorCore Hs D₂ D n)) (dGammaCoreOp Hs D₂ A D)
--
--   Formalization note: Lean 4 identifier `BookProof.SecondQuantizationCore.dGamma_essentiallySelfAdjointOn_fockCore`.

-- Generated from ChapterSecondQuantizationCoreEsa.lean — theorem BookProof.SecondQuantizationCore.dGamma_essentiallySelfAdjointOn_fockCore
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
open BookProof.DirectSumEsa
open BookProof.GraphCore
open BookProof.TensorCore
open BookProof.SecondQuantizationCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore BookProof.DirectSumEsa

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.SecondQuantizationCore.dGamma_essentiallySelfAdjointOn_fockCore (hcore : IsGraphCore D A)
    (hsector : ∀ n : ℕ,
      EssentiallySelfAdjointOn (fockSectorDom Hs D₂ n) (fockSectorOp Hs D₂ A n)) :
    EssentiallySelfAdjointOn (dsCore (fun n : ℕ => fockSectorCore Hs D₂ D n))
      (dGammaCoreOp Hs D₂ A D) := by sorry
