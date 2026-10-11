-- Prove2me | Theorems.Thm_BookProof_SmCar_car_annih_annih
-- name    : BookProof.SmCar.car_annih_annih
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T13:27:12.601878+00:00
-- url     : https://prove2.me/theorems/fdea446f-23dc-4d1d-9313-b00407be7b54
-- title:
--   `BookProof.SmCar.car_annih_annih` (i j : Fin n) : annih i ∘ₗ annih j + annih j ∘ₗ annih i = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmCarAlgebra`.
--
--   `BookProof.SmCar.car_annih_annih` (i j : Fin n) : annih i ∘ₗ annih j + annih j ∘ₗ annih i = 0
--
--   Formalization note: Lean 4 identifier `BookProof.SmCar.car_annih_annih`.

-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.car_annih_annih
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.SmCar



open Finset

variable {n : ℕ}

theorem BookProof.SmCar.car_annih_annih (i j : Fin n) :
    annih i ∘ₗ annih j + annih j ∘ₗ annih i = 0 := by sorry
