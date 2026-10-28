-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_jump_affine_cutoff_generator_eq_drift
-- name    : AvramDividend.Classical.zero_jump_affine_cutoff_generator_eq_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:30:42.498048+00:00
-- url     : https://prove2.me/theorems/91b7fca0-cf5c-4d6a-89f7-c63a04127d8f
-- title:
--   Zero-jump Lévy generator of the zero-extended affine candidate equals drift at positive reserves
-- statement:
--   At each strictly positive reserve the zero-extended affine candidate has derivative one and second derivative zero. When the Lévy jump measure vanishes, the jump generator integrand is integrable and integrates to zero. Hence the canonical Lévy generator equals the drift coefficient, an HJB ingredient in the Brownian counterexample audit.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), Section 4 generator; earlier formalized cutoff derivatives.

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_affine_cutoff_deriv_eq_one_positive
import Theorems.Thm_AvramDividend_Classical_affine_cutoff_second_deriv_eq_zero_positive

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.zero_jump_affine_cutoff_generator_eq_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (y : ℝ) (hy : 0 < y) :
    X.GeneratorIntegrable (fun z : ℝ => if z < 0 then 0 else z - 1) y ∧
      X.generator (fun z : ℝ => if z < 0 then 0 else z - 1) y = X.c := by sorry
