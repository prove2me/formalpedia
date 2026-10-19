-- Prove2me | Theorems.Thm_BookProof_SmCar_norm_creat_le
-- name    : BookProof.SmCar.norm_creat_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T23:00:47.901034+00:00
-- url     : https://prove2.me/theorems/d2fb2be2-b49c-4f74-9ae2-087dda24ae2e
-- title:
--   `BookProof.SmCar.norm_creat_le` (i : Fin n) (ψ : FermiFock n) : ‖creat i ψ‖ ≤ ‖ψ‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmCarAlgebra`.
--
--   `BookProof.SmCar.norm_creat_le` (i : Fin n) (ψ : FermiFock n) : ‖creat i ψ‖ ≤ ‖ψ‖
--
--   Formalization note: Lean 4 identifier `BookProof.SmCar.norm_creat_le`.

-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.norm_creat_le
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.SmCar



open Finset

variable {n : ℕ}

theorem BookProof.SmCar.norm_creat_le (i : Fin n) (ψ : FermiFock n) : ‖creat i ψ‖ ≤ ‖ψ‖ := by sorry
