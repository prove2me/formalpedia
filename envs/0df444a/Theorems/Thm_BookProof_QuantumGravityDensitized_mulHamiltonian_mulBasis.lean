-- Prove2me | Theorems.Thm_BookProof_QuantumGravityDensitized_mulHamiltonian_mulBasis
-- name    : BookProof.QuantumGravityDensitized.mulHamiltonian_mulBasis
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T05:05:14.444915+00:00
-- url     : https://prove2.me/theorems/087f38b0-bc93-4d70-9ab8-22c10143c6ea
-- title:
--   The Lean 4 theorem `mulHamiltonian_mulBasis` in the `ChapterQuantumGravityDensitized` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.QuantumGravityDensitized.mulHamiltonian_mulBasis` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterQuantumGravityDensitized.lean — theorem BookProof.QuantumGravityDensitized.mulHamiltonian_mulBasis
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterFarisLavine
open BookProof.FarisLavine
open BookProof.QuantumGravityDensitized



open Filter Topology BookProof.FarisLavine

theorem BookProof.QuantumGravityDensitized.mulHamiltonian_mulBasis (lam : ℕ → ℝ) (n : ℕ) :
    (mulHamiltonian lam (mulBasis lam n) : L2Nat) = lp.single 2 n ((lam n : ℂ)) := by sorry
