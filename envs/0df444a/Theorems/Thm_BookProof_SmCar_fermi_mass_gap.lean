-- Prove2me | Theorems.Thm_BookProof_SmCar_fermi_mass_gap
-- name    : BookProof.SmCar.fermi_mass_gap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:28:12.072367+00:00
-- url     : https://prove2.me/theorems/c15dea39-93b5-4f9c-b00d-061348529d06
-- title:
--   `BookProof.SmCar.fermi_mass_gap` {m : Fin n → ℝ} {mu : ℝ} (hmu : 0 ≤ mu) (hm : ∀ i, mu ≤ m i) (ψ : FermiFock n) (hvac : ψ ∅ = 0) : mu * ‖ψ‖ ^ 2 ≤ (inner ℂ ψ (fermiEnergy...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmCarAlgebra`.
--
--   `BookProof.SmCar.fermi_mass_gap` {m : Fin n → ℝ} {mu : ℝ} (hmu : 0 ≤ mu) (hm : ∀ i, mu ≤ m i) (ψ : FermiFock n) (hvac : ψ ∅ = 0) : mu * ‖ψ‖ ^ 2 ≤ (inner ℂ ψ (fermiEnergy m ψ) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.SmCar.fermi_mass_gap`.

-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.fermi_mass_gap
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar



open Finset

variable {n : ℕ}

theorem BookProof.SmCar.fermi_mass_gap {m : Fin n → ℝ} {mu : ℝ} (hmu : 0 ≤ mu) (hm : ∀ i, mu ≤ m i)
    (ψ : FermiFock n) (hvac : ψ ∅ = 0) :
    mu * ‖ψ‖ ^ 2 ≤ (inner ℂ ψ (fermiEnergy m ψ) : ℂ).re := by sorry
