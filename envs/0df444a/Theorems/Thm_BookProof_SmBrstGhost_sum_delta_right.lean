-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_sum_delta_right
-- name    : BookProof.SmBrstGhost.sum_delta_right
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:00:36.725886+00:00
-- url     : https://prove2.me/theorems/9e1293f5-7b3e-4cb1-968f-1f119fcd62c7
-- title:
--   `BookProof.SmBrstGhost.sum_delta_right` (M P : Matrix (Fin N) (Fin N) ℂ) : ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, (M i j * P k l) • (if l = i then (creat k * annih j :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.sum_delta_right` (M P : Matrix (Fin N) (Fin N) ℂ) : ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, (M i j * P k l) • (if l = i then (creat k * annih j : Module.End ℂ (FermiFock N)) else 0) = fermiBilin (P * M)
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.sum_delta_right`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.sum_delta_right
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

theorem BookProof.SmBrstGhost.sum_delta_right (M P : Matrix (Fin N) (Fin N) ℂ) :
    ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
        (M i j * P k l) • (if l = i then (creat k * annih j : Module.End ℂ (FermiFock N)) else 0)
      = fermiBilin (P * M) := by sorry
