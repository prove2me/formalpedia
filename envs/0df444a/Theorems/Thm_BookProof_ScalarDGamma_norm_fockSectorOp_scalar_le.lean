-- Prove2me | Theorems.Thm_BookProof_ScalarDGamma_norm_fockSectorOp_scalar_le
-- name    : BookProof.ScalarDGamma.norm_fockSectorOp_scalar_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-25T02:16:01.749982+00:00
-- url     : https://prove2.me/theorems/9fcd2091-b210-44cc-acdc-151ee29daba4
-- title:
--   `BookProof.ScalarDGamma.norm_fockSectorOp_scalar_le` (n : ℕ) (x : fockSectorDom Hs ⊤ n) : ‖fockSectorOp Hs ⊤ (scalarOp Hs c) n x‖ ≤ ((n : ℝ) * |c|) * ‖(x : fockSector Hs n)‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalarDGammaEsa`.
--
--   `BookProof.ScalarDGamma.norm_fockSectorOp_scalar_le` (n : ℕ) (x : fockSectorDom Hs ⊤ n) : ‖fockSectorOp Hs ⊤ (scalarOp Hs c) n x‖ ≤ ((n : ℝ) * |c|) * ‖(x : fockSector Hs n)‖
--
--   Formalization note: Lean 4 identifier `BookProof.ScalarDGamma.norm_fockSectorOp_scalar_le`.

-- Generated from ChapterScalarDGammaEsa.lean — theorem BookProof.ScalarDGamma.norm_fockSectorOp_scalar_le
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterScalarDGammaEsa
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

theorem BookProof.ScalarDGamma.norm_fockSectorOp_scalar_le (n : ℕ) (x : fockSectorDom Hs ⊤ n) :
    ‖fockSectorOp Hs ⊤ (scalarOp Hs c) n x‖ ≤ ((n : ℝ) * |c|) * ‖(x : fockSector Hs n)‖ := by sorry
