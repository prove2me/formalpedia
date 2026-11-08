-- Prove2me | Theorems.Thm_BookProof_QuantumGravityDensitized_densTetrad_det
-- name    : BookProof.QuantumGravityDensitized.densTetrad_det
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T00:25:45.483209+00:00
-- url     : https://prove2.me/theorems/4fd53891-61e1-4dcc-9ae6-2b828e145d4a
-- title:
--   The Lean 4 theorem `densTetrad_det` in the `ChapterQuantumGravityDensitized` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `densTetrad_det` in the `ChapterQuantumGravityDensitized` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravityDensitized.lean

-- Generated from ChapterQuantumGravityDensitized.lean — theorem BookProof.QuantumGravityDensitized.densTetrad_det
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterBddBelowFiberSumEsa
open BookProof.QuantumGravityDensitized



open Filter Topology BookProof.FarisLavine

theorem BookProof.QuantumGravityDensitized.densTetrad_det (E : Matrix (Fin 3) (Fin 3) ℝ) :
    (densTetrad E).det = Real.sqrt E.det ^ 3 * E.det := by sorry
