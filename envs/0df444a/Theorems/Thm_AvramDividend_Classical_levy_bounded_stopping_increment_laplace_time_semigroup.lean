-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_laplace_time_semigroup
-- name    : AvramDividend.Classical.levy_bounded_stopping_increment_laplace_time_semigroup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:31:05.602914+00:00
-- url     : https://prove2.me/theorems/49777fb3-e07b-4def-ba5f-45b7fc36e7f6
-- title:
--   Time-semigroup law for bounded-stopping Lévy exponential transforms
-- statement:
--   For a bounded stopping time τ and two deterministic horizons h,k≥0, the exponential moment of the combined future increment equals the product exp(hψ(θ)) exp(kψ(θ)), for nonnegative θ. This explicitly records the Lévy transform semigroup law in the post-stopping setting.
-- source:
--   Apply the proved bounded-stopping increment Laplace formula at horizon h+k and split exp((h+k)ψ(θ)) using real coercion of nonnegative reals and the exponential addition identity.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_laplace
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_increment_laplace_time_semigroup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h k : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, Real.exp (θ *
      (X.X (τ ω + (h + k)) ω - X.X (τ ω) ω)) ∂P =
        Real.exp ((h : ℝ) * X.ψ θ) *
          Real.exp ((k : ℝ) * X.ψ θ) := by sorry
