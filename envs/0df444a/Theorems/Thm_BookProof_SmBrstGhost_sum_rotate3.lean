-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_sum_rotate3
-- name    : BookProof.SmBrstGhost.sum_rotate3
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:09:15.674992+00:00
-- url     : https://prove2.me/theorems/f71ac9ea-f566-4b9b-8b77-7331221f8f0e
-- title:
--   `BookProof.SmBrstGhost.sum_rotate3` {M : Type*} [AddCommMonoid M] {n : ℕ} (F : Fin n → Fin n → Fin n → M) : ∑ d : Fin n, ∑ g : Fin n, ∑ a : Fin n, F a d g = ∑ a : Fin n, ∑ d : Fin
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.sum_rotate3` {M : Type*} [AddCommMonoid M] {n : ℕ} (F : Fin n → Fin n → Fin n → M) : ∑ d : Fin n, ∑ g : Fin n, ∑ a : Fin n, F a d g = ∑ a : Fin n, ∑ d : Fin n, ∑ g : Fin n, F a d g
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.sum_rotate3`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.sum_rotate3
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

variable {m : ℕ}
variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}

theorem BookProof.SmBrstGhost.sum_rotate3 {M : Type*} [AddCommMonoid M] {n : ℕ} (F : Fin n → Fin n → Fin n → M) :
    ∑ d : Fin n, ∑ g : Fin n, ∑ a : Fin n, F a d g
      = ∑ a : Fin n, ∑ d : Fin n, ∑ g : Fin n, F a d g := by sorry
