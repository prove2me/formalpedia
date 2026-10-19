-- Prove2me | Theorems.Thm_BookProof_ChapterA_IsRReal_not_hasCommutingRImaginary
-- name    : BookProof.ChapterA.IsRReal.not_hasCommutingRImaginary
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:12:19.457821+00:00
-- url     : https://prove2.me/theorems/091364ec-b028-4b88-8fac-56495f611b94
-- title:
--   `BookProof.ChapterA.IsRReal.not_hasCommutingRImaginary` [Nontrivial W] {M : System ℝ W} (h : IsRReal M) : ¬ HasCommutingRImaginary M
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1h`.
--
--   `BookProof.ChapterA.IsRReal.not_hasCommutingRImaginary` [Nontrivial W] {M : System ℝ W} (h : IsRReal M) : ¬ HasCommutingRImaginary M
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.IsRReal.not_hasCommutingRImaginary`.

-- Generated from ChapterA1h.lean — theorem BookProof.ChapterA.IsRReal.not_hasCommutingRImaginary
import Definitions.Def_Complexification
import Mathlib
import Definitions.Def_ChapterA1h
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


open BookProof.Complexification

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem BookProof.ChapterA.IsRReal.not_hasCommutingRImaginary [Nontrivial W] {M : System ℝ W}
    (h : IsRReal M) : ¬ HasCommutingRImaginary M := by sorry
