-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_hasDerivAt_exp_mul
-- name    : BookProof.ChapterSoftmaxFluctuation.hasDerivAt_exp_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:16:03.360178+00:00
-- url     : https://prove2.me/theorems/72a3247e-5c77-4e50-8d4d-629ea6f940bd
-- title:
--   `BookProof.ChapterSoftmaxFluctuation.hasDerivAt_exp_mul` (beta c : ℝ) : HasDerivAt (fun b : ℝ => Real.exp (b * c)) (c * Real.exp (beta * c)) beta
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxFluctuation`.
--
--   `BookProof.ChapterSoftmaxFluctuation.hasDerivAt_exp_mul` (beta c : ℝ) : HasDerivAt (fun b : ℝ => Real.exp (b * c)) (c * Real.exp (beta * c)) beta
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxFluctuation.hasDerivAt_exp_mul`.

-- Generated from ChapterSoftmaxFluctuation.lean — theorem BookProof.ChapterSoftmaxFluctuation.hasDerivAt_exp_mul
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterSoftmaxFluctuation


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxFluctuation.hasDerivAt_exp_mul (beta c : ℝ) :
    HasDerivAt (fun b : ℝ => Real.exp (b * c)) (c * Real.exp (beta * c)) beta := by sorry
