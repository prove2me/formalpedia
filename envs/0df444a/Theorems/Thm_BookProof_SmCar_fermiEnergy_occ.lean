-- Prove2me | Theorems.Thm_BookProof_SmCar_fermiEnergy_occ
-- name    : BookProof.SmCar.fermiEnergy_occ
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:27:59.487703+00:00
-- url     : https://prove2.me/theorems/e526eab4-63d9-4efe-9ad8-ca99220bb898
-- title:
--   `BookProof.SmCar.fermiEnergy_occ` (m : Fin n → ℝ) (S : Finset (Fin n)) : fermiEnergy m (occ S) = ((∑ i ∈ S, m i : ℝ) : ℂ) • occ S
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmCarAlgebra`.
--
--   `BookProof.SmCar.fermiEnergy_occ` (m : Fin n → ℝ) (S : Finset (Fin n)) : fermiEnergy m (occ S) = ((∑ i ∈ S, m i : ℝ) : ℂ) • occ S
--
--   Formalization note: Lean 4 identifier `BookProof.SmCar.fermiEnergy_occ`.

-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.fermiEnergy_occ
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar



open Finset

variable {n : ℕ}

theorem BookProof.SmCar.fermiEnergy_occ (m : Fin n → ℝ) (S : Finset (Fin n)) :
    fermiEnergy m (occ S) = ((∑ i ∈ S, m i : ℝ) : ℂ) • occ S := by sorry
