-- Prove2me | Theorems.Thm_BookProof_QuantumGravityDensitized_christoffel_eq_zero_of_const
-- name    : BookProof.QuantumGravityDensitized.christoffel_eq_zero_of_const
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T00:25:37.962072+00:00
-- url     : https://prove2.me/theorems/e2ae1ef8-4094-4cc1-9816-7ce0e69cfcc5
-- title:
--   The Lean 4 theorem `christoffel_eq_zero_of_const` in the `ChapterQuantumGravityDensitized` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `christoffel_eq_zero_of_const` in the `ChapterQuantumGravityDensitized` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravityDensitized.lean

-- Generated from ChapterQuantumGravityDensitized.lean — theorem BookProof.QuantumGravityDensitized.christoffel_eq_zero_of_const
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterBddBelowFiberSumEsa
open BookProof.QuantumGravityDensitized



open Filter Topology BookProof.FarisLavine

theorem BookProof.QuantumGravityDensitized.christoffel_eq_zero_of_const {m : ℕ} (g0 : Matrix (Fin m) (Fin m) ℝ)
    (ginv : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (q : EuclideanSpace ℝ (Fin m)) (k i j : Fin m) :
    christoffel (fun _ => g0) ginv q k i j = 0 := by sorry
