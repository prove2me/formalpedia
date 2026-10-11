-- Prove2me | Theorems.Thm_BookProof_SmCar_car_annih_creat_self
-- name    : BookProof.SmCar.car_annih_creat_self
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T13:26:59.603413+00:00
-- url     : https://prove2.me/theorems/f5b5d936-2d98-4e8d-9d21-a811fb87a258
-- title:
--   `BookProof.SmCar.car_annih_creat_self` (i : Fin n) : annih i ∘ₗ creat i + creat i ∘ₗ annih i = LinearMap.id
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmCarAlgebra`.
--
--   `BookProof.SmCar.car_annih_creat_self` (i : Fin n) : annih i ∘ₗ creat i + creat i ∘ₗ annih i = LinearMap.id
--
--   Formalization note: Lean 4 identifier `BookProof.SmCar.car_annih_creat_self`.

-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.car_annih_creat_self
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.SmCar



open Finset

variable {n : ℕ}

theorem BookProof.SmCar.car_annih_creat_self (i : Fin n) :
    annih i ∘ₗ creat i + creat i ∘ₗ annih i = LinearMap.id := by sorry
