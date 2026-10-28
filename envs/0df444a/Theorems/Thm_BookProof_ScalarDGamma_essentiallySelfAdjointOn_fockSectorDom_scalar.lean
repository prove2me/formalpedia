-- Prove2me | Theorems.Thm_BookProof_ScalarDGamma_essentiallySelfAdjointOn_fockSectorDom_scalar
-- name    : BookProof.ScalarDGamma.essentiallySelfAdjointOn_fockSectorDom_scalar
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-25T02:15:34.121792+00:00
-- url     : https://prove2.me/theorems/4311af6a-e139-4957-a2e0-41001c0eaf85
-- title:
--   `BookProof.ScalarDGamma.essentiallySelfAdjointOn_fockSectorDom_scalar` (n : ℕ) : EssentiallySelfAdjointOn (fockSectorDom Hs ⊤ n) (fockSectorOp Hs ⊤ (scalarOp Hs c) n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalarDGammaEsa`.
--
--   `BookProof.ScalarDGamma.essentiallySelfAdjointOn_fockSectorDom_scalar` (n : ℕ) : EssentiallySelfAdjointOn (fockSectorDom Hs ⊤ n) (fockSectorOp Hs ⊤ (scalarOp Hs c) n)
--
--   Formalization note: Lean 4 identifier `BookProof.ScalarDGamma.essentiallySelfAdjointOn_fockSectorDom_scalar`.

-- Generated from ChapterScalarDGammaEsa.lean — theorem BookProof.ScalarDGamma.essentiallySelfAdjointOn_fockSectorDom_scalar
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterScalarDGammaEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterScalarDGammaEsa
open BookProof.TensorCore
open BookProof.ScalarDGamma



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.SecondQuantizationCore

noncomputable section

variable (Hs : IPSpace) (c : ℝ)

theorem BookProof.ScalarDGamma.essentiallySelfAdjointOn_fockSectorDom_scalar (n : ℕ) :
    EssentiallySelfAdjointOn (fockSectorDom Hs ⊤ n) (fockSectorOp Hs ⊤ (scalarOp Hs c) n) := by sorry
