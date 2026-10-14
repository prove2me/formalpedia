-- Prove2me | Theorems.Thm_BookProof_SecondQuantizationCore_essentiallySelfAdjointOn_fockSectorCore
-- name    : BookProof.SecondQuantizationCore.essentiallySelfAdjointOn_fockSectorCore
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:49:40.256977+00:00
-- url     : https://prove2.me/theorems/1bfbbc7f-8c95-470a-9b81-07741a1030e1
-- title:
--   `BookProof.SecondQuantizationCore.essentiallySelfAdjointOn_fockSectorCore` (hcore : IsGraphCore D A) (n : ℕ) (hesa : EssentiallySelfAdjointOn (fockSectorDom Hs D₂ n) (fockSectorOp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSecondQuantizationCoreEsa`.
--
--   `BookProof.SecondQuantizationCore.essentiallySelfAdjointOn_fockSectorCore` (hcore : IsGraphCore D A) (n : ℕ) (hesa : EssentiallySelfAdjointOn (fockSectorDom Hs D₂ n) (fockSectorOp Hs D₂ A n)) : EssentiallySelfAdjointOn (fockSectorCore Hs D₂ D n) (restrictOp (fockSectorOp Hs D₂ A n) (fockSectorCore_le_fockSectorDom Hs D₂ D n))
--
--   Formalization note: Lean 4 identifier `BookProof.SecondQuantizationCore.essentiallySelfAdjointOn_fockSectorCore`.

-- Generated from ChapterSecondQuantizationCoreEsa.lean — theorem BookProof.SecondQuantizationCore.essentiallySelfAdjointOn_fockSectorCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Mathlib
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
open BookProof.GraphCore
open BookProof.TensorCore
open BookProof.SecondQuantizationCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore BookProof.DirectSumEsa

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.SecondQuantizationCore.essentiallySelfAdjointOn_fockSectorCore (hcore : IsGraphCore D A) (n : ℕ)
    (hesa : EssentiallySelfAdjointOn (fockSectorDom Hs D₂ n) (fockSectorOp Hs D₂ A n)) :
    EssentiallySelfAdjointOn (fockSectorCore Hs D₂ D n)
      (restrictOp (fockSectorOp Hs D₂ A n) (fockSectorCore_le_fockSectorDom Hs D₂ D n)) := by sorry
