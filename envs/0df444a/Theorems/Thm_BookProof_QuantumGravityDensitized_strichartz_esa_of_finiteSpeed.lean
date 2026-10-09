-- Prove2me | Theorems.Thm_BookProof_QuantumGravityDensitized_strichartz_esa_of_finiteSpeed
-- name    : BookProof.QuantumGravityDensitized.strichartz_esa_of_finiteSpeed
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T23:23:55.1077+00:00
-- url     : https://prove2.me/theorems/b084dfab-5931-45f4-b8d9-9634abfef59f
-- title:
--   The Lean 4 theorem `strichartz_esa_of_finiteSpeed` in the `ChapterQuantumGravityDensitized` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.QuantumGravityDensitized.strichartz_esa_of_finiteSpeed` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterQuantumGravityDensitized.lean — theorem BookProof.QuantumGravityDensitized.strichartz_esa_of_finiteSpeed
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterFarisLavineCore
open BookProof.QuantumGravityDensitized



open Filter Topology BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.QuantumGravityDensitized.strichartz_esa_of_finiteSpeed {D : Submodule ℂ F} (H : D →ₗ[ℂ] F)
    (finiteSpeed : ∀ z : ℂ, z.im ≠ 0 → DeficiencyTrivialAt D H z) :
    EssentiallySelfAdjointOn D H := by sorry
