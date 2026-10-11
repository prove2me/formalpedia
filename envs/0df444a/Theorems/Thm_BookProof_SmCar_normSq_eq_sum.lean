-- Prove2me | Theorems.Thm_BookProof_SmCar_normSq_eq_sum
-- name    : BookProof.SmCar.normSq_eq_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:26:46.172857+00:00
-- url     : https://prove2.me/theorems/5b9de677-1a52-4d2c-884f-a5d28b9576b6
-- title:
--   `BookProof.SmCar.normSq_eq_sum` (x : FermiFock n) : ‖x‖ ^ 2 = ∑ S : Finset (Fin n), ‖x S‖ ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmCarAlgebra`.
--
--   `BookProof.SmCar.normSq_eq_sum` (x : FermiFock n) : ‖x‖ ^ 2 = ∑ S : Finset (Fin n), ‖x S‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.SmCar.normSq_eq_sum`.

-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.normSq_eq_sum
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar



open Finset

variable {n : ℕ}

theorem BookProof.SmCar.normSq_eq_sum (x : FermiFock n) :
    ‖x‖ ^ 2 = ∑ S : Finset (Fin n), ‖x S‖ ^ 2 := by sorry
