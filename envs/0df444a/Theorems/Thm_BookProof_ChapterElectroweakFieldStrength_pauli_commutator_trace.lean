-- Prove2me | Theorems.Thm_BookProof_ChapterElectroweakFieldStrength_pauli_commutator_trace
-- name    : BookProof.ChapterElectroweakFieldStrength.pauli_commutator_trace
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T02:44:30.023807+00:00
-- url     : https://prove2.me/theorems/bebcb531-ed1e-4d55-bc5b-151016031134
-- title:
--   `BookProof.ChapterElectroweakFieldStrength.pauli_commutator_trace` (k l j : Fin 3) : ((pauliV k * pauliV l - pauliV l * pauliV k) * pauliV j).trace = 4 * Complex.I * eps k l j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterElectroweakFieldStrength`.
--
--   `BookProof.ChapterElectroweakFieldStrength.pauli_commutator_trace` (k l j : Fin 3) : ((pauliV k * pauliV l - pauliV l * pauliV k) * pauliV j).trace = 4 * Complex.I * eps k l j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterElectroweakFieldStrength.pauli_commutator_trace`.

-- Generated from ChapterElectroweakFieldStrength.lean — theorem BookProof.ChapterElectroweakFieldStrength.pauli_commutator_trace
import Definitions.Def_ChapterParity
import Mathlib
import Definitions.Def_ChapterElectroweakFieldStrength
import Definitions.Def_ChapterParitySU2
open BookProof.ChapterParitySU2
open BookProof.ChapterElectroweakFieldStrength


open Matrix


open BookProof.ChapterParity BookProof.ChapterParitySU2

theorem BookProof.ChapterElectroweakFieldStrength.pauli_commutator_trace (k l j : Fin 3) :
    ((pauliV k * pauliV l - pauliV l * pauliV k) * pauliV j).trace = 4 * Complex.I * eps k l j := by sorry
