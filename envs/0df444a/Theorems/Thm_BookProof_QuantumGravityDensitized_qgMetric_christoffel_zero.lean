-- Prove2me | Theorems.Thm_BookProof_QuantumGravityDensitized_qgMetric_christoffel_zero
-- name    : BookProof.QuantumGravityDensitized.qgMetric_christoffel_zero
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T00:29:59.874142+00:00
-- url     : https://prove2.me/theorems/e9f0d867-b2a4-4dab-9379-2276b5867e51
-- title:
--   The Lean 4 theorem `qgMetric_christoffel_zero` in the `ChapterQuantumGravityDensitized` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgMetric_christoffel_zero` in the `ChapterQuantumGravityDensitized` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravityDensitized.lean

-- Generated from ChapterQuantumGravityDensitized.lean — theorem BookProof.QuantumGravityDensitized.qgMetric_christoffel_zero
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterBddBelowFiberSumEsa
open BookProof.QuantumGravityDensitized



open Filter Topology BookProof.FarisLavine

theorem BookProof.QuantumGravityDensitized.qgMetric_christoffel_zero {n : ℕ}
    (ginv : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (q : EuclideanSpace ℝ (Fin (n + 1))) (k i j : Fin (n + 1)) :
    christoffel (fun _ => qgMetric n) ginv q k i j = 0 := by sorry
