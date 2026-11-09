-- Prove2me | Theorems.Thm_BookProof_QuantumGravityDensitized_qgMetric_det
-- name    : BookProof.QuantumGravityDensitized.qgMetric_det
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T00:26:34.726677+00:00
-- url     : https://prove2.me/theorems/e980b46e-ee7c-4ec8-b1f3-bdf33afb4a2c
-- title:
--   The Lean 4 theorem `qgMetric_det` in the `ChapterQuantumGravityDensitized` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgMetric_det` in the `ChapterQuantumGravityDensitized` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravityDensitized.lean

-- Generated from ChapterQuantumGravityDensitized.lean — theorem BookProof.QuantumGravityDensitized.qgMetric_det
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterBddBelowFiberSumEsa
open BookProof.QuantumGravityDensitized



open Filter Topology BookProof.FarisLavine

theorem BookProof.QuantumGravityDensitized.qgMetric_det (n : ℕ) :
    (qgMetric n).det = ∏ i, (if i = Fin.last n then -(1 / 24) else 1 / 16 : ℝ) := by sorry
