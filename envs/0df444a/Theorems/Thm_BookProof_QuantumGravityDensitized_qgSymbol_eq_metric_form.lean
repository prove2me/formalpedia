-- Prove2me | Theorems.Thm_BookProof_QuantumGravityDensitized_qgSymbol_eq_metric_form
-- name    : BookProof.QuantumGravityDensitized.qgSymbol_eq_metric_form
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T00:26:42.383484+00:00
-- url     : https://prove2.me/theorems/e422cdda-336d-4b14-b0e1-7d39a607983e
-- title:
--   The Lean 4 theorem `qgSymbol_eq_metric_form` in the `ChapterQuantumGravityDensitized` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgSymbol_eq_metric_form` in the `ChapterQuantumGravityDensitized` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravityDensitized.lean

-- Generated from ChapterQuantumGravityDensitized.lean — theorem BookProof.QuantumGravityDensitized.qgSymbol_eq_metric_form
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterBddBelowFiberSumEsa
open BookProof.QuantumGravityDensitized



open Filter Topology BookProof.FarisLavine

theorem BookProof.QuantumGravityDensitized.qgSymbol_eq_metric_form {n : ℕ} (xi : Fin n → ℝ) (xiY : ℝ) :
    qgSymbol xi xiY
      = ∑ i, ∑ j, qgMetric n i j * qgMomenta xi xiY i * qgMomenta xi xiY j := by sorry
