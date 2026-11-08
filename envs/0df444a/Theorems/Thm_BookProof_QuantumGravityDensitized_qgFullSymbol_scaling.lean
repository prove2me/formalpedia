-- Prove2me | Theorems.Thm_BookProof_QuantumGravityDensitized_qgFullSymbol_scaling
-- name    : BookProof.QuantumGravityDensitized.qgFullSymbol_scaling
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T00:29:22.38324+00:00
-- url     : https://prove2.me/theorems/95bb0aac-30ca-4546-a3e7-80fe31d0b2b3
-- title:
--   The Lean 4 theorem `qgFullSymbol_scaling` in the `ChapterQuantumGravityDensitized` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgFullSymbol_scaling` in the `ChapterQuantumGravityDensitized` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravityDensitized.lean

-- Generated from ChapterQuantumGravityDensitized.lean — theorem BookProof.QuantumGravityDensitized.qgFullSymbol_scaling
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterBddBelowFiberSumEsa
open BookProof.QuantumGravityDensitized



open Filter Topology BookProof.FarisLavine

theorem BookProof.QuantumGravityDensitized.qgFullSymbol_scaling {n : ℕ} (c : ℝ) (xi : Fin n → ℝ) (xiY : ℝ)
    (b : Fin n → ℝ) (bY : ℝ) (V : ℝ) :
    qgFullSymbol (fun a => c * xi a) (c * xiY) b bY V
      = c ^ 2 * qgSymbol xi xiY + c * ((∑ a, b a * xi a) + bY * xiY) - V := by sorry
