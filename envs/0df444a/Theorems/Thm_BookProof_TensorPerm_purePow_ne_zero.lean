-- Prove2me | Theorems.Thm_BookProof_TensorPerm_purePow_ne_zero
-- name    : BookProof.TensorPerm.purePow_ne_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:05:24.687468+00:00
-- url     : https://prove2.me/theorems/65f2a186-5337-4c36-b480-ef3e19092d9e
-- title:
--   `BookProof.TensorPerm.purePow_ne_zero` {n : ℕ} {f : Fin n → E.carrier} (hf : ∀ i, f i ≠ 0) : purePow E n f ≠ 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorPermutation`.
--
--   `BookProof.TensorPerm.purePow_ne_zero` {n : ℕ} {f : Fin n → E.carrier} (hf : ∀ i, f i ≠ 0) : purePow E n f ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.TensorPerm.purePow_ne_zero`.

-- Generated from ChapterTensorPermutation.lean — theorem BookProof.TensorPerm.purePow_ne_zero
import Definitions.Def_ChapterGroupAverageEsa
import Mathlib
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterTensorGraphCore
open BookProof.TensorCore
open BookProof.TensorPerm



open scoped TensorProduct
open BookProof.TensorCore BookProof.GroupAverage

noncomputable section

variable (E : BookProof.TensorCore.IPSpace)

theorem BookProof.TensorPerm.purePow_ne_zero {n : ℕ} {f : Fin n → E.carrier} (hf : ∀ i, f i ≠ 0) :
    purePow E n f ≠ 0 := by sorry
