-- Prove2me | Theorems.Thm_BookProof_SmCar_sum_apply_fock
-- name    : BookProof.SmCar.sum_apply_fock
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:26:44.234464+00:00
-- url     : https://prove2.me/theorems/632037c2-0e68-4816-8991-a940ac801421
-- title:
--   `BookProof.SmCar.sum_apply_fock` (f : Fin n → FermiFock n) (S : Finset (Fin n)) : (∑ i : Fin n, f i) S = ∑ i : Fin n, (f i) S
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmCarAlgebra`.
--
--   `BookProof.SmCar.sum_apply_fock` (f : Fin n → FermiFock n) (S : Finset (Fin n)) : (∑ i : Fin n, f i) S = ∑ i : Fin n, (f i) S
--
--   Formalization note: Lean 4 identifier `BookProof.SmCar.sum_apply_fock`.

-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.sum_apply_fock
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar



open Finset

variable {n : ℕ}

theorem BookProof.SmCar.sum_apply_fock (f : Fin n → FermiFock n) (S : Finset (Fin n)) :
    (∑ i : Fin n, f i) S = ∑ i : Fin n, (f i) S := by sorry
