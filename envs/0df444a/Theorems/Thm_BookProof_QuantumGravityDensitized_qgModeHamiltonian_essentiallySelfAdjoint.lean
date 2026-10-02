-- Prove2me | Theorems.Thm_BookProof_QuantumGravityDensitized_qgModeHamiltonian_essentiallySelfAdjoint
-- name    : BookProof.QuantumGravityDensitized.qgModeHamiltonian_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T06:28:16.394657+00:00
-- url     : https://prove2.me/theorems/9a04c830-74a1-4a13-a17a-791ef0b4a167
-- title:
--   qgModeHamiltonian_essentiallySelfAdjoint
-- statement:
--   Formal statement of `BookProof.QuantumGravityDensitized.qgModeHamiltonian_essentiallySelfAdjoint` from the timepiece Lean 4 formalization (source chapter `BookProof/ChapterQuantumGravityDensitized.lean`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravityDensitized.lean

-- Generated from ChapterQuantumGravityDensitized.lean — theorem BookProof.QuantumGravityDensitized.qgModeHamiltonian_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine
open BookProof.QuantumGravityDensitized



open Filter Topology BookProof.FarisLavine

theorem BookProof.QuantumGravityDensitized.qgModeHamiltonian_essentiallySelfAdjoint (a b V : ℕ → ℝ) :
    EssentiallySelfAdjointOn (mulSymbolDomain (qgModeSymbol a b V)) (qgModeHamiltonian a b V) := by sorry
