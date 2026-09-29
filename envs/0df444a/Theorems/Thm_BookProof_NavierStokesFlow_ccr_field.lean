-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ccr_field
-- name    : BookProof.NavierStokesFlow.ccr_field
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:28:34.982494+00:00
-- url     : https://prove2.me/theorems/12ea54d6-c2e5-4513-ba8b-fefb9ffed0de
-- title:
--   The Lean 4 theorem `ccr_field` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ccr_field` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.ccr_field
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

theorem BookProof.NavierStokesFlow.ccr_field {σ : Type*} [DecidableEq σ] (a b : σ) (p : MvPolynomial σ ℂ) :
    (MvPolynomial.pderiv a) (MvPolynomial.X b * p)
      - MvPolynomial.X b * (MvPolynomial.pderiv a) p = (if a = b then p else 0) := by sorry
