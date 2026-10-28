-- Prove2me | Theorems.Thm_BookProof_ScalarDGamma_dense_fockSectorDom
-- name    : BookProof.ScalarDGamma.dense_fockSectorDom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-25T02:15:32.366849+00:00
-- url     : https://prove2.me/theorems/df7d78f5-a2c6-435e-942a-32e820ab6f5f
-- title:
--   `BookProof.ScalarDGamma.dense_fockSectorDom` (n : ℕ) : Dense ((fockSectorDom Hs ⊤ n : Submodule ℂ (fockSector Hs n)) : Set (fockSector Hs n))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalarDGammaEsa`.
--
--   `BookProof.ScalarDGamma.dense_fockSectorDom` (n : ℕ) : Dense ((fockSectorDom Hs ⊤ n : Submodule ℂ (fockSector Hs n)) : Set (fockSector Hs n))
--
--   Formalization note: Lean 4 identifier `BookProof.ScalarDGamma.dense_fockSectorDom`.

-- Generated from ChapterScalarDGammaEsa.lean — theorem BookProof.ScalarDGamma.dense_fockSectorDom
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterScalarDGammaEsa
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterScalarDGammaEsa
open BookProof.GraphCore
open BookProof.TensorCore
open BookProof.ScalarDGamma



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.SecondQuantizationCore

noncomputable section

variable (Hs : IPSpace) (c : ℝ)

theorem BookProof.ScalarDGamma.dense_fockSectorDom (n : ℕ) :
    Dense ((fockSectorDom Hs ⊤ n : Submodule ℂ (fockSector Hs n)) :
      Set (fockSector Hs n)) := by sorry
