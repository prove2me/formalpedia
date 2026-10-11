-- Prove2me | Theorems.Thm_BookProof_SmCar_norm_annih_le
-- name    : BookProof.SmCar.norm_annih_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T23:00:17.068164+00:00
-- url     : https://prove2.me/theorems/71f6476b-ce00-4d57-b1d4-522cdfa6cbd2
-- title:
--   `BookProof.SmCar.norm_annih_le` (i : Fin n) (ψ : FermiFock n) : ‖annih i ψ‖ ≤ ‖ψ‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmCarAlgebra`.
--
--   `BookProof.SmCar.norm_annih_le` (i : Fin n) (ψ : FermiFock n) : ‖annih i ψ‖ ≤ ‖ψ‖
--
--   Formalization note: Lean 4 identifier `BookProof.SmCar.norm_annih_le`.

-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.norm_annih_le
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.SmCar



open Finset

variable {n : ℕ}

theorem BookProof.SmCar.norm_annih_le (i : Fin n) (ψ : FermiFock n) : ‖annih i ψ‖ ≤ ‖ψ‖ := by sorry
