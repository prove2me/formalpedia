-- Prove2me | Theorems.Thm_BookProof_SmCar_car_annih_creat_of_ne
-- name    : BookProof.SmCar.car_annih_creat_of_ne
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T13:27:27.616704+00:00
-- url     : https://prove2.me/theorems/f6835a89-771e-4343-87c0-f7a0ec30369c
-- title:
--   `BookProof.SmCar.car_annih_creat_of_ne` {i j : Fin n} (hij : i ≠ j) : annih i ∘ₗ creat j + creat j ∘ₗ annih i = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmCarAlgebra`.
--
--   `BookProof.SmCar.car_annih_creat_of_ne` {i j : Fin n} (hij : i ≠ j) : annih i ∘ₗ creat j + creat j ∘ₗ annih i = 0
--
--   Formalization note: Lean 4 identifier `BookProof.SmCar.car_annih_creat_of_ne`.

-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.car_annih_creat_of_ne
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.SmCar



open Finset

variable {n : ℕ}

theorem BookProof.SmCar.car_annih_creat_of_ne {i j : Fin n} (hij : i ≠ j) :
    annih i ∘ₗ creat j + creat j ∘ₗ annih i = 0 := by sorry
