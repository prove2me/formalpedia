-- Prove2me | Theorems.Thm_BookProof_TensorPerm_inner_purePow
-- name    : BookProof.TensorPerm.inner_purePow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:05:14.394974+00:00
-- url     : https://prove2.me/theorems/d47afbe8-fcd0-4cee-8506-5eff3040bbb1
-- title:
--   `BookProof.TensorPerm.inner_purePow` : ∀ (n : ℕ) (f g : Fin n → E.carrier), (inner ℂ (purePow E n f) (purePow E n g) : ℂ) = ∏ i, inner ℂ (f i) (g i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorPermutation`.
--
--   `BookProof.TensorPerm.inner_purePow` : ∀ (n : ℕ) (f g : Fin n → E.carrier), (inner ℂ (purePow E n f) (purePow E n g) : ℂ) = ∏ i, inner ℂ (f i) (g i)
--
--   Formalization note: Lean 4 identifier `BookProof.TensorPerm.inner_purePow`.

-- Generated from ChapterTensorPermutation.lean — theorem BookProof.TensorPerm.inner_purePow
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

theorem BookProof.TensorPerm.inner_purePow : ∀ (n : ℕ) (f g : Fin n → E.carrier),
    (inner ℂ (purePow E n f) (purePow E n g) : ℂ) = ∏ i, inner ℂ (f i) (g i) := by sorry
