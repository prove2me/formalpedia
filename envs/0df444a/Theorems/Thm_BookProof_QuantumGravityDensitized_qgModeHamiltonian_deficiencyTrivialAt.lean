-- Prove2me | Theorems.Thm_BookProof_QuantumGravityDensitized_qgModeHamiltonian_deficiencyTrivialAt
-- name    : BookProof.QuantumGravityDensitized.qgModeHamiltonian_deficiencyTrivialAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T06:28:02.811542+00:00
-- url     : https://prove2.me/theorems/4fe569f6-36ac-4047-912d-93e8c05c9e4b
-- title:
--   qgModeHamiltonian_deficiencyTrivialAt
-- statement:
--   Formal statement of `BookProof.QuantumGravityDensitized.qgModeHamiltonian_deficiencyTrivialAt` from the timepiece Lean 4 formalization (source chapter `BookProof/ChapterQuantumGravityDensitized.lean`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravityDensitized.lean

-- Generated from ChapterQuantumGravityDensitized.lean — theorem BookProof.QuantumGravityDensitized.qgModeHamiltonian_deficiencyTrivialAt
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine
open BookProof.QuantumGravityDensitized



open Filter Topology BookProof.FarisLavine

theorem BookProof.QuantumGravityDensitized.qgModeHamiltonian_deficiencyTrivialAt (a b V : ℕ → ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (mulSymbolDomain (qgModeSymbol a b V)) (qgModeHamiltonian a b V) z := by sorry
