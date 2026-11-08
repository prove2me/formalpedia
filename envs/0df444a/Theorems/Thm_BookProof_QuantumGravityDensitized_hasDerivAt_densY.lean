-- Prove2me | Theorems.Thm_BookProof_QuantumGravityDensitized_hasDerivAt_densY
-- name    : BookProof.QuantumGravityDensitized.hasDerivAt_densY
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T00:26:29.808615+00:00
-- url     : https://prove2.me/theorems/738ecdcf-3d4a-4b89-9649-07f3d2ee2873
-- title:
--   The Lean 4 theorem `hasDerivAt_densY` in the `ChapterQuantumGravityDensitized` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hasDerivAt_densY` in the `ChapterQuantumGravityDensitized` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravityDensitized.lean

-- Generated from ChapterQuantumGravityDensitized.lean — theorem BookProof.QuantumGravityDensitized.hasDerivAt_densY
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterBddBelowFiberSumEsa
open BookProof.QuantumGravityDensitized



open Filter Topology BookProof.FarisLavine

theorem BookProof.QuantumGravityDensitized.hasDerivAt_densY {e : ℝ} (he : e ≠ 0) :
    HasDerivAt densY (1 / (2 * Real.sqrt e)) e := by sorry
