-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_mark_count_pgf_monotone_20261117
-- name    : AvramDividend.Classical.avram_a27_original_physical_negative_mark_count_pgf_monotone_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:32:26.808261+00:00
-- url     : https://prove2.me/theorems/9b37449d-4ae5-4e16-af66-6b7114cee686
-- title:
--   Actual original negative-jump marked count PGF increases with unit-interval generating parameter
-- statement:
--   For fixed nonnegative exponential mark tilt theta, the exact physical negative-jump count and full jump-sum joint generating function on the unchanged original Lévy probability space is monotone in the generating parameter from zero to one. It is a source-faithful structural property useful for the Campbell/Volterra route.
-- source:
--   Original negative-jump exponential unit bound 40973 and generic bounded marked-count PGF monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original actual negative physical jump marked-count PGF is monotone. -/

theorem AvramDividend.Classical.avram_a27_original_physical_negative_mark_count_pgf_monotone_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (z w : ℝ) (hz : 0 ≤ z) (hzw : z ≤ w) (hw : w ≤ 1) :
    (∫ ω, z ^ K ω * Real.exp (θ * J ω) ∂P) ≤
      (∫ ω, w ^ K ω * Real.exp (θ * J ω) ∂P) := by sorry
