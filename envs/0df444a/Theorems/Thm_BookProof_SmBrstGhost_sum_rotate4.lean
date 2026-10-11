-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_sum_rotate4
-- name    : BookProof.SmBrstGhost.sum_rotate4
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:09:19.091984+00:00
-- url     : https://prove2.me/theorems/69a1f144-c636-419c-b259-7c5dbfe98de5
-- title:
--   `BookProof.SmBrstGhost.sum_rotate4` {M : Type*} [AddCommMonoid M] {n : ℕ} (F : Fin n → Fin n → Fin n → Fin n → M) : ∑ d : Fin n, ∑ g : Fin n, ∑ h : Fin n, ∑ a : Fin n, F a d g h =
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.sum_rotate4` {M : Type*} [AddCommMonoid M] {n : ℕ} (F : Fin n → Fin n → Fin n → Fin n → M) : ∑ d : Fin n, ∑ g : Fin n, ∑ h : Fin n, ∑ a : Fin n, F a d g h = ∑ a : Fin n, ∑ d : Fin n, ∑ g : Fin n, ∑ h : Fin n, F a d g h
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.sum_rotate4`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.sum_rotate4
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

theorem BookProof.SmBrstGhost.sum_rotate4 {M : Type*} [AddCommMonoid M] {n : ℕ} (F : Fin n → Fin n → Fin n → Fin n → M) :
    ∑ d : Fin n, ∑ g : Fin n, ∑ h : Fin n, ∑ a : Fin n, F a d g h
      = ∑ a : Fin n, ∑ d : Fin n, ∑ g : Fin n, ∑ h : Fin n, F a d g h := by sorry
