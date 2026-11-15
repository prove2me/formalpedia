-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a78_original_positive_time_tilt_physical_jump_poisson_laplace_20261114
-- name    : AvramDividend.Classical.avram_a78_original_positive_time_tilt_physical_jump_poisson_laplace_20261114
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T13:24:16.38937+00:00
-- url     : https://prove2.me/theorems/3884581f-6577-42a8-ae9f-23f3599581fa
-- title:
--   Original actual negative-jump compound Poisson Laplace at strictly positive horizon and strictly positive tilt
-- statement:
--   The exact original-source finite negative-jump compound Poisson marginal Laplace law, narrowed to strictly positive horizon and tilt. Under the original SpectrallyNegativeLevy assumptions and an a.e. physical jump-total representative J, this is the irreducible original marked Poisson Laplace transform. The omitted endpoint cases, t=0 and theta=0, have elementary direct proofs in the A77 parent. This child involves no same-space Gaussian companion and no BV assumption.
-- source:
--   Lévy-Ito original finite negative marked jump Poisson law, positive time and tilt; original band moment/mark process laws. Parent A77 handles zero horizons and tilts explicitly.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a78_original_positive_time_tilt_physical_jump_poisson_laplace_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (ht : 0 < t) (θ : ℝ) (hθ : 0 < θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0) :
    (∫ ω, Real.exp (θ * J ω) ∂P) =
      Real.exp ((t : ℝ) *
        (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν)) := by sorry
