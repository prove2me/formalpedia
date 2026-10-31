-- Prove2me | Theorems.Thm_BookProof_QuantumGravityDensitized_strichartz_finiteSpeed_satisfiable
-- name    : BookProof.QuantumGravityDensitized.strichartz_finiteSpeed_satisfiable
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T12:07:07.748661+00:00
-- url     : https://prove2.me/theorems/25831398-3567-4e27-bc7d-e220ff43e5c2
-- title:
--   The Lean 4 theorem `strichartz_finiteSpeed_satisfiable` in the `ChapterQuantumGravityDensitized` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `strichartz_finiteSpeed_satisfiable` in the `ChapterQuantumGravityDensitized` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravityDensitized.lean

-- Generated from ChapterQuantumGravityDensitized.lean — theorem BookProof.QuantumGravityDensitized.strichartz_finiteSpeed_satisfiable
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine
open BookProof.QuantumGravityDensitized



open Filter Topology BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.QuantumGravityDensitized.strichartz_finiteSpeed_satisfiable (a b V : ℕ → ℝ) :
    EssentiallySelfAdjointOn (mulSymbolDomain (qgModeSymbol a b V)) (qgModeHamiltonian a b V) := by sorry
