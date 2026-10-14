-- Prove2me | Theorems.Thm_BookProof_SecondQuantizationCore_isGraphCore_fockSectorCore
-- name    : BookProof.SecondQuantizationCore.isGraphCore_fockSectorCore
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:48:42.431186+00:00
-- url     : https://prove2.me/theorems/b2d93eac-ed18-46ff-8184-b2f5cd2fe0c5
-- title:
--   `BookProof.SecondQuantizationCore.isGraphCore_fockSectorCore` (hcore : IsGraphCore D A) (n : ℕ) : IsGraphCore (fockSectorCore Hs D₂ D n) (fockSectorOp Hs D₂ A n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSecondQuantizationCoreEsa`.
--
--   `BookProof.SecondQuantizationCore.isGraphCore_fockSectorCore` (hcore : IsGraphCore D A) (n : ℕ) : IsGraphCore (fockSectorCore Hs D₂ D n) (fockSectorOp Hs D₂ A n)
--
--   Formalization note: Lean 4 identifier `BookProof.SecondQuantizationCore.isGraphCore_fockSectorCore`.

-- Generated from ChapterSecondQuantizationCoreEsa.lean — theorem BookProof.SecondQuantizationCore.isGraphCore_fockSectorCore
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterDirectSumEsa
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

theorem BookProof.SecondQuantizationCore.isGraphCore_fockSectorCore (hcore : IsGraphCore D A) (n : ℕ) :
    IsGraphCore (fockSectorCore Hs D₂ D n) (fockSectorOp Hs D₂ A n) := by sorry
