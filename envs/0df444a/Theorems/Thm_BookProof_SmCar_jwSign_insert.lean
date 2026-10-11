-- Prove2me | Theorems.Thm_BookProof_SmCar_jwSign_insert
-- name    : BookProof.SmCar.jwSign_insert
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:26:59.285655+00:00
-- url     : https://prove2.me/theorems/b07ef7d7-3e19-4f48-bded-32229e8fcd3a
-- title:
--   `BookProof.SmCar.jwSign_insert` {i j : Fin n} {S : Finset (Fin n)} (hj : j ∉ S) : jwSign i (insert j S) = (if j < i then -1 else 1) * jwSign i S
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmCarAlgebra`.
--
--   `BookProof.SmCar.jwSign_insert` {i j : Fin n} {S : Finset (Fin n)} (hj : j ∉ S) : jwSign i (insert j S) = (if j < i then -1 else 1) * jwSign i S
--
--   Formalization note: Lean 4 identifier `BookProof.SmCar.jwSign_insert`.

-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.jwSign_insert
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar



open Finset

variable {n : ℕ}

theorem BookProof.SmCar.jwSign_insert {i j : Fin n} {S : Finset (Fin n)} (hj : j ∉ S) :
    jwSign i (insert j S) = (if j < i then -1 else 1) * jwSign i S := by sorry
