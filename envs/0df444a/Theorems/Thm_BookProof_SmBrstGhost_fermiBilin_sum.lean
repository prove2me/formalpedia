-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_fermiBilin_sum
-- name    : BookProof.SmBrstGhost.fermiBilin_sum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T17:47:59.679652+00:00
-- url     : https://prove2.me/theorems/77482c4c-8269-470f-a65d-078fee1c1797
-- title:
--   `BookProof.SmBrstGhost.fermiBilin_sum` {ι : Type*} (s : Finset ι) (M : ι → Matrix (Fin N) (Fin N) ℂ) : (fermiBilin (∑ t ∈ s, M t) : Module.End ℂ (FermiFock N)) = ∑ t ∈ s, fermiBili
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.fermiBilin_sum` {ι : Type*} (s : Finset ι) (M : ι → Matrix (Fin N) (Fin N) ℂ) : (fermiBilin (∑ t ∈ s, M t) : Module.End ℂ (FermiFock N)) = ∑ t ∈ s, fermiBilin (M t)
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.fermiBilin_sum`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.fermiBilin_sum
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

theorem BookProof.SmBrstGhost.fermiBilin_sum {ι : Type*} (s : Finset ι) (M : ι → Matrix (Fin N) (Fin N) ℂ) :
    (fermiBilin (∑ t ∈ s, M t) : Module.End ℂ (FermiFock N))
      = ∑ t ∈ s, fermiBilin (M t) := by sorry
