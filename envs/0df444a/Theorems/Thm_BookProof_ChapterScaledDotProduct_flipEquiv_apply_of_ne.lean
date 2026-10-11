-- Prove2me | Theorems.Thm_BookProof_ChapterScaledDotProduct_flipEquiv_apply_of_ne
-- name    : BookProof.ChapterScaledDotProduct.flipEquiv_apply_of_ne
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:43:51.899844+00:00
-- url     : https://prove2.me/theorems/0bbe5305-4017-4ec2-9059-9811799fbbbe
-- title:
--   `BookProof.ChapterScaledDotProduct.flipEquiv_apply_of_ne` {i j : Fin d} (h : j ≠ i) (x : Fin d → Bool) : (flipEquiv i x) j = x j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScaledDotProduct`.
--
--   `BookProof.ChapterScaledDotProduct.flipEquiv_apply_of_ne` {i j : Fin d} (h : j ≠ i) (x : Fin d → Bool) : (flipEquiv i x) j = x j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterScaledDotProduct.flipEquiv_apply_of_ne`.

-- Generated from ChapterScaledDotProduct.lean — theorem BookProof.ChapterScaledDotProduct.flipEquiv_apply_of_ne
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterScaledDotProduct
open BookProof.ChapterScaledDotProduct


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness

variable {d : ℕ}

theorem BookProof.ChapterScaledDotProduct.flipEquiv_apply_of_ne {i j : Fin d} (h : j ≠ i) (x : Fin d → Bool) :
    (flipEquiv i x) j = x j := by sorry
