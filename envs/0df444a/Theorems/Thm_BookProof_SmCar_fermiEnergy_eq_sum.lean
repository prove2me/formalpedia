-- Prove2me | Theorems.Thm_BookProof_SmCar_fermiEnergy_eq_sum
-- name    : BookProof.SmCar.fermiEnergy_eq_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:27:59.468119+00:00
-- url     : https://prove2.me/theorems/1c828928-88f1-43c5-bcf0-e96a25bde3a4
-- title:
--   `BookProof.SmCar.fermiEnergy_eq_sum` (m : Fin n → ℝ) (ψ : FermiFock n) : fermiEnergy m ψ = ∑ i : Fin n, (m i : ℂ) • creat i (annih i ψ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmCarAlgebra`.
--
--   `BookProof.SmCar.fermiEnergy_eq_sum` (m : Fin n → ℝ) (ψ : FermiFock n) : fermiEnergy m ψ = ∑ i : Fin n, (m i : ℂ) • creat i (annih i ψ)
--
--   Formalization note: Lean 4 identifier `BookProof.SmCar.fermiEnergy_eq_sum`.

-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.fermiEnergy_eq_sum
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.SmCar



open Finset

variable {n : ℕ}

theorem BookProof.SmCar.fermiEnergy_eq_sum (m : Fin n → ℝ) (ψ : FermiFock n) :
    fermiEnergy m ψ = ∑ i : Fin n, (m i : ℂ) • creat i (annih i ψ) := by sorry
