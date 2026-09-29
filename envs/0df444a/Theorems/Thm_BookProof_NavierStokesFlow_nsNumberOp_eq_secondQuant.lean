-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsNumberOp_eq_secondQuant
-- name    : BookProof.NavierStokesFlow.nsNumberOp_eq_secondQuant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:53:37.526462+00:00
-- url     : https://prove2.me/theorems/49c0f463-76ba-41fe-baed-a58a85dd940a
-- title:
--   The Lean 4 theorem `nsNumberOp_eq_secondQuant` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsNumberOp_eq_secondQuant` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.nsNumberOp_eq_secondQuant
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

variable {n : ℕ}

theorem BookProof.NavierStokesFlow.nsNumberOp_eq_secondQuant {m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ) :
    nsNumberOp A = nsSecondQuant A 1 := by sorry
