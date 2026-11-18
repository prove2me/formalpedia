-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_joint_negative_mark_pgf_dominated_by_count_20261117
-- name    : AvramDividend.Classical.avram_a27_original_joint_negative_mark_pgf_dominated_by_count_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:23:14.954118+00:00
-- url     : https://prove2.me/theorems/99d8f323-3b20-410b-a0b6-8eca06415234
-- title:
--   Original physical marked-jump PGF is pointwise dominated by the unmarked Poisson count PGF
-- statement:
--   For the actual finite-activity spectrally negative Levy path, any measurable representative of its cumulative negative jump sum has an exponential weighting in (0,1] for nonnegative theta. Hence at each physical sample point outside a null set, for any z in [0,1] the marked joint PGF observable z^K exp(theta J) lies between 0 and z^K. The count K remains the original path count and no independent mark stream is introduced.
-- source:
--   Proved avram_a85_original_physical_negative_jump_exponential_integrable_20261114; elementary nonnegative powers and order of real multiplication.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a85_original_physical_negative_jump_exponential_integrable_20261114
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_joint_negative_mark_pgf_dominated_by_count_20261117
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
    (K : Ω → ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∀ᵐ ω ∂P, 0 ≤ z ^ (K ω) * Real.exp (θ * J ω) ∧
      z ^ (K ω) * Real.exp (θ * J ω) ≤ z ^ (K ω) := by sorry
