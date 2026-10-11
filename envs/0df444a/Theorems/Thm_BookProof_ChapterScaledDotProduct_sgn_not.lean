-- Prove2me | Theorems.Thm_BookProof_ChapterScaledDotProduct_sgn_not
-- name    : BookProof.ChapterScaledDotProduct.sgn_not
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:42:59.434333+00:00
-- url     : https://prove2.me/theorems/0a885e36-b917-49c4-b020-47d26145f52e
-- title:
--   `BookProof.ChapterScaledDotProduct.sgn_not` (b : Bool) : sgn (!b) = -sgn b
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScaledDotProduct`.
--
--   `BookProof.ChapterScaledDotProduct.sgn_not` (b : Bool) : sgn (!b) = -sgn b
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterScaledDotProduct.sgn_not`.

-- Generated from ChapterScaledDotProduct.lean — theorem BookProof.ChapterScaledDotProduct.sgn_not
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterScaledDotProduct
open BookProof.ChapterScaledDotProduct


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness

variable {d : ℕ}

theorem BookProof.ChapterScaledDotProduct.sgn_not (b : Bool) : sgn (!b) = -sgn b := by sorry
