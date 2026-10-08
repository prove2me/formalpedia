-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_fermiBilin_comm_annih
-- name    : BookProof.SmBrstGhost.fermiBilin_comm_annih
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T13:00:50.162292+00:00
-- url     : https://prove2.me/theorems/8ac932ef-981a-4727-a1f3-918a4b4f2a42
-- title:
--   `BookProof.SmBrstGhost.fermiBilin_comm_annih` {A : Matrix (Fin N) (Fin N) ℂ} {k : Fin N} (hrow : ∀ j, A k j = 0) : (fermiBilin A : Module.End ℂ (FermiFock N)) * annih k = annih k *
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.fermiBilin_comm_annih` {A : Matrix (Fin N) (Fin N) ℂ} {k : Fin N} (hrow : ∀ j, A k j = 0) : (fermiBilin A : Module.End ℂ (FermiFock N)) * annih k = annih k * fermiBilin A
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.fermiBilin_comm_annih`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.fermiBilin_comm_annih
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

theorem BookProof.SmBrstGhost.fermiBilin_comm_annih {A : Matrix (Fin N) (Fin N) ℂ} {k : Fin N}
    (hrow : ∀ j, A k j = 0) :
    (fermiBilin A : Module.End ℂ (FermiFock N)) * annih k
      = annih k * fermiBilin A := by sorry
