-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_sum_delta_left
-- name    : BookProof.SmBrstGhost.sum_delta_left
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:00:19.394436+00:00
-- url     : https://prove2.me/theorems/207cdcc0-687c-4ab6-a784-b2640e45c4ee
-- title:
--   `BookProof.SmBrstGhost.sum_delta_left` (M P : Matrix (Fin N) (Fin N) ℂ) : ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, (M i j * P k l) • (if j = k then (creat i * annih l :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.sum_delta_left` (M P : Matrix (Fin N) (Fin N) ℂ) : ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, (M i j * P k l) • (if j = k then (creat i * annih l : Module.End ℂ (FermiFock N)) else 0) = fermiBilin (M * P)
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.sum_delta_left`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.sum_delta_left
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

variable {m : ℕ}
variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {N : ℕ}

theorem BookProof.SmBrstGhost.sum_delta_left (M P : Matrix (Fin N) (Fin N) ℂ) :
    ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
        (M i j * P k l) • (if j = k then (creat i * annih l : Module.End ℂ (FermiFock N)) else 0)
      = fermiBilin (M * P) := by sorry
