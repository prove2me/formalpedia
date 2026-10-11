-- Prove2me | Theorems.Thm_BookProof_SmCar_occupation_apply
-- name    : BookProof.SmCar.occupation_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T23:00:29.928219+00:00
-- url     : https://prove2.me/theorems/aa060857-1033-4f1f-821d-e6b0e0289e0f
-- title:
--   `BookProof.SmCar.occupation_apply` (i : Fin n) (ψ : FermiFock n) (S : Finset (Fin n)) : (creat i (annih i ψ)) S = if i ∈ S then ψ S else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmCarAlgebra`.
--
--   `BookProof.SmCar.occupation_apply` (i : Fin n) (ψ : FermiFock n) (S : Finset (Fin n)) : (creat i (annih i ψ)) S = if i ∈ S then ψ S else 0
--
--   Formalization note: Lean 4 identifier `BookProof.SmCar.occupation_apply`.

-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.occupation_apply
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.SmCar



open Finset

variable {n : ℕ}

theorem BookProof.SmCar.occupation_apply (i : Fin n) (ψ : FermiFock n) (S : Finset (Fin n)) :
    (creat i (annih i ψ)) S = if i ∈ S then ψ S else 0 := by sorry
