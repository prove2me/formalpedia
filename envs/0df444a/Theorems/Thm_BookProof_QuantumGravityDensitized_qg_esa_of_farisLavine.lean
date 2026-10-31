-- Prove2me | Theorems.Thm_BookProof_QuantumGravityDensitized_qg_esa_of_farisLavine
-- name    : BookProof.QuantumGravityDensitized.qg_esa_of_farisLavine
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T22:46:34.292556+00:00
-- url     : https://prove2.me/theorems/2fbff3e1-f45f-4850-91db-e4823f20ea25
-- title:
--   The Lean 4 theorem `qg_esa_of_farisLavine` in the `ChapterQuantumGravityDensitized` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qg_esa_of_farisLavine` in the `ChapterQuantumGravityDensitized` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravityDensitized.lean

-- Generated from ChapterQuantumGravityDensitized.lean — theorem BookProof.QuantumGravityDensitized.qg_esa_of_farisLavine
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterBddBelowFiberSumEsa
open BookProof.QuantumGravityDensitized



open Filter Topology BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.QuantumGravityDensitized.qg_esa_of_farisLavine {D : Submodule ℂ F} (H N : D →ₗ[ℂ] F) (c : ℝ)
    (hH : SymmetricOn D H) (hN : SymmetricOn D N) (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hNsurj : ∀ f : F, ∃ x : D, N x + (x : F) = f)
    (hcomm : ∀ x : D, |commForm H N x| ≤ c * quadForm N x) :
    EssentiallySelfAdjointOn D H := by sorry
