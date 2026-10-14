-- Prove2me | Theorems.Thm_BookProof_SmCar_fermiEnergy_quadForm
-- name    : BookProof.SmCar.fermiEnergy_quadForm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:28:23.251658+00:00
-- url     : https://prove2.me/theorems/38a4d32a-165e-4a52-a485-935670245c2a
-- title:
--   `BookProof.SmCar.fermiEnergy_quadForm` (m : Fin n → ℝ) (ψ : FermiFock n) : (inner ℂ ψ (fermiEnergy m ψ) : ℂ) = ∑ S : Finset (Fin n), ((∑ i ∈ S, m i : ℝ) : ℂ) * ((‖ψ S‖ ^...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmCarAlgebra`.
--
--   `BookProof.SmCar.fermiEnergy_quadForm` (m : Fin n → ℝ) (ψ : FermiFock n) : (inner ℂ ψ (fermiEnergy m ψ) : ℂ) = ∑ S : Finset (Fin n), ((∑ i ∈ S, m i : ℝ) : ℂ) * ((‖ψ S‖ ^ 2 : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.SmCar.fermiEnergy_quadForm`.

-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.fermiEnergy_quadForm
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar



open Finset

variable {n : ℕ}

theorem BookProof.SmCar.fermiEnergy_quadForm (m : Fin n → ℝ) (ψ : FermiFock n) :
    (inner ℂ ψ (fermiEnergy m ψ) : ℂ)
      = ∑ S : Finset (Fin n), ((∑ i ∈ S, m i : ℝ) : ℂ) * ((‖ψ S‖ ^ 2 : ℝ) : ℂ) := by sorry
