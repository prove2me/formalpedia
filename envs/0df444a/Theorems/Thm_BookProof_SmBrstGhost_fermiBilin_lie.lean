-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_fermiBilin_lie
-- name    : BookProof.SmBrstGhost.fermiBilin_lie
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:09:57.488809+00:00
-- url     : https://prove2.me/theorems/7e87e33c-0366-4ba7-951b-888e53e3fa06
-- title:
--   `BookProof.SmBrstGhost.fermiBilin_lie` (A B : Matrix (Fin N) (Fin N) ℂ) : (fermiBilin A : Module.End ℂ (FermiFock N)) * fermiBilin B - fermiBilin B * fermiBilin A = fermiBilin (A *
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.fermiBilin_lie` (A B : Matrix (Fin N) (Fin N) ℂ) : (fermiBilin A : Module.End ℂ (FermiFock N)) * fermiBilin B - fermiBilin B * fermiBilin A = fermiBilin (A * B - B * A)
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.fermiBilin_lie`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.fermiBilin_lie
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.SmCar
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

variable {m : ℕ}
variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {N : ℕ}

theorem BookProof.SmBrstGhost.fermiBilin_lie (A B : Matrix (Fin N) (Fin N) ℂ) :
    (fermiBilin A : Module.End ℂ (FermiFock N)) * fermiBilin B
        - fermiBilin B * fermiBilin A
      = fermiBilin (A * B - B * A) := by sorry
