-- Prove2me | Theorems.Thm_BookProof_SmCar_jwSign_mul_self
-- name    : BookProof.SmCar.jwSign_mul_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:27:21.984987+00:00
-- url     : https://prove2.me/theorems/c3ffb3a9-1d51-4d1a-92b5-a8502bc67b97
-- title:
--   `BookProof.SmCar.jwSign_mul_self` (i : Fin n) (S : Finset (Fin n)) : jwSign i S * jwSign i S = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmCarAlgebra`.
--
--   `BookProof.SmCar.jwSign_mul_self` (i : Fin n) (S : Finset (Fin n)) : jwSign i S * jwSign i S = 1
--
--   Formalization note: Lean 4 identifier `BookProof.SmCar.jwSign_mul_self`.

-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.jwSign_mul_self
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar



open Finset

variable {n : ℕ}

theorem BookProof.SmCar.jwSign_mul_self (i : Fin n) (S : Finset (Fin n)) : jwSign i S * jwSign i S = 1 := by sorry
