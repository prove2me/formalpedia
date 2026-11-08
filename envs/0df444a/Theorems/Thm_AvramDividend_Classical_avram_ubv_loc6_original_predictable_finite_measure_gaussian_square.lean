-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_predictable_finite_measure_gaussian_square
-- name    : AvramDividend.Classical.avram_ubv_loc6_original_predictable_finite_measure_gaussian_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:39:43.048638+00:00
-- url     : https://prove2.me/theorems/a1bb1872-48a5-4e7c-8683-d729150e3905
-- title:
--   Same predictable-measure finite square-energy from a compact original Gaussian coefficient bound
-- statement:
--   For the exact Gaussian variance coefficient X.σ of the original spectrally negative Lévy source, any nonnegative discount rate q, any C² candidate w on its actual below-cap interior, a clipped predictable-time reserve U restricted to a compact interior band, and any finite original predictable measure μ, there is one finite uniform coefficient bound and the square-energy Lebesgue integral on this same predictable μ is finite. No measurability-space coercion or stopped Gaussian centring is assumed.
-- source:
--   Original X.σ with real nonnegative time and source band; Proved Mathlib compact C² derivative bound e6632b80 and IsOpen b917eaf2. Pointwise squared-coefficient dominance yields finite lintegral on the actual predictable σ-algebra.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_source_interior_compact_derivative_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A bounded original discounted Gaussian derivative coefficient has finite
    square energy on any finite predictable measure, with no change of sigma algebra. -/

theorem AvramDividend.Classical.avram_ubv_loc6_original_predictable_finite_measure_gaussian_square
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hband : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (U : ℝ≥0 × Ω → ℝ) (hU : ∀ p, U p ∈ Icc a b) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ p : ℝ≥0 × Ω,
        |Real.exp (-(q * (p.1 : ℝ))) * (X.σ * deriv w (U p))| ≤ K) ∧
      (∫⁻ p, ENNReal.ofReal
        ((Real.exp (-(q * (p.1 : ℝ))) * (X.σ * deriv w (U p))) ^ 2) ∂μ) < ⊤ := by sorry
