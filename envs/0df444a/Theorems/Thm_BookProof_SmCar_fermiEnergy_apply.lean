-- Prove2me | Theorems.Thm_BookProof_SmCar_fermiEnergy_apply
-- name    : BookProof.SmCar.fermiEnergy_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:28:08.542365+00:00
-- url     : https://prove2.me/theorems/af237104-20e9-43d9-be4f-ea6ceceac13b
-- title:
--   `BookProof.SmCar.fermiEnergy_apply` (m : Fin n → ℝ) (ψ : FermiFock n) (S : Finset (Fin n)) : (fermiEnergy m ψ) S = ((∑ i ∈ S, m i : ℝ) : ℂ) * ψ S
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmCarAlgebra`.
--
--   `BookProof.SmCar.fermiEnergy_apply` (m : Fin n → ℝ) (ψ : FermiFock n) (S : Finset (Fin n)) : (fermiEnergy m ψ) S = ((∑ i ∈ S, m i : ℝ) : ℂ) * ψ S
--
--   Formalization note: Lean 4 identifier `BookProof.SmCar.fermiEnergy_apply`.

-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.fermiEnergy_apply
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.SmCar



open Finset

variable {n : ℕ}

theorem BookProof.SmCar.fermiEnergy_apply (m : Fin n → ℝ) (ψ : FermiFock n) (S : Finset (Fin n)) :
    (fermiEnergy m ψ) S = ((∑ i ∈ S, m i : ℝ) : ℂ) * ψ S := by sorry
