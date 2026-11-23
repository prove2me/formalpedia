-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_degenerate_original_physical_poisson_moment
-- name    : AvramDividend.Classical.avram_bridge20261123_A77_degenerate_original_physical_poisson_moment
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T15:28:51.649179+00:00
-- url     : https://prove2.me/theorems/c5cff476-7ec3-4ca2-90a6-281eca79bf88
-- title:
--   Original physical negative-jump Poisson moment in zero-measure, zero-time or zero-Laplace cases
-- statement:
--   When the original negative Levy jump measure is zero, the time horizon is zero, or the Laplace argument is zero, the actual exponential jump-sum payoff is almost surely one and the Levy mark exponent vanishes. Select a genuinely Poisson-distributed source count from the Proved original Borel count law and take mark moment m=1 to obtain the entire original source moment model.
-- source:
--   A77 exact physical moment model 9262691d; Proved original negative Borel Poisson law 54bd238b; Proved original zero-Levy physical jump vanishing e847d9a7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_A77_degenerate_original_physical_poisson_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0)
    (hDeg : X.ν = 0 ∨ t = 0 ∨ θ = 0) :
    ∃ (N : Ω → ℕ) (r : ℝ≥0) (m : ℝ),
      HasLaw N (poissonMeasure r) P ∧
      (∫ ω, Real.exp (θ * J ω) ∂P) =
        ∫ ω, m ^ (N ω) ∂P ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) *
          (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν) := by sorry
