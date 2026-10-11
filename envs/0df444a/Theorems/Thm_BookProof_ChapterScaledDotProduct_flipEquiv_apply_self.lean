-- Prove2me | Theorems.Thm_BookProof_ChapterScaledDotProduct_flipEquiv_apply_self
-- name    : BookProof.ChapterScaledDotProduct.flipEquiv_apply_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:43:37.336142+00:00
-- url     : https://prove2.me/theorems/d741f4a3-48a5-44a7-bf84-1a4c7144ecb2
-- title:
--   `BookProof.ChapterScaledDotProduct.flipEquiv_apply_self` (i : Fin d) (x : Fin d → Bool) : (flipEquiv i x) i = !(x i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScaledDotProduct`.
--
--   `BookProof.ChapterScaledDotProduct.flipEquiv_apply_self` (i : Fin d) (x : Fin d → Bool) : (flipEquiv i x) i = !(x i)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterScaledDotProduct.flipEquiv_apply_self`.

-- Generated from ChapterScaledDotProduct.lean — theorem BookProof.ChapterScaledDotProduct.flipEquiv_apply_self
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterScaledDotProduct
open BookProof.ChapterScaledDotProduct


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness

variable {d : ℕ}

theorem BookProof.ChapterScaledDotProduct.flipEquiv_apply_self (i : Fin d) (x : Fin d → Bool) :
    (flipEquiv i x) i = !(x i) := by sorry
