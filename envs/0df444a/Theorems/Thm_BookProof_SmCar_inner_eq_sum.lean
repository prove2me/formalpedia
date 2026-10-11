-- Prove2me | Theorems.Thm_BookProof_SmCar_inner_eq_sum
-- name    : BookProof.SmCar.inner_eq_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:26:19.591299+00:00
-- url     : https://prove2.me/theorems/0b5d6722-86c0-4817-a636-0959f4af829e
-- title:
--   `BookProof.SmCar.inner_eq_sum` (x y : FermiFock n) : (inner ℂ x y : ℂ) = ∑ S : Finset (Fin n), (starRingEnd ℂ) (x S) * y S
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmCarAlgebra`.
--
--   `BookProof.SmCar.inner_eq_sum` (x y : FermiFock n) : (inner ℂ x y : ℂ) = ∑ S : Finset (Fin n), (starRingEnd ℂ) (x S) * y S
--
--   Formalization note: Lean 4 identifier `BookProof.SmCar.inner_eq_sum`.

-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.inner_eq_sum
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar



open Finset

variable {n : ℕ}

theorem BookProof.SmCar.inner_eq_sum (x y : FermiFock n) :
    (inner ℂ x y : ℂ) = ∑ S : Finset (Fin n), (starRingEnd ℂ) (x S) * y S := by sorry
