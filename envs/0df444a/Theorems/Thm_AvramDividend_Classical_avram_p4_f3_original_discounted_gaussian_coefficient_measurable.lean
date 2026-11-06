-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_gaussian_coefficient_measurable
-- name    : AvramDividend.Classical.avram_p4_f3_original_discounted_gaussian_coefficient_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:18:50.192232+00:00
-- url     : https://prove2.me/theorems/9befa605-da97-4c5b-a914-43847fc71677
-- title:
--   Actual original clipped predividend Gaussian discounted Ito coefficient is jointly Borel measurable
-- statement:
--   For the same original spectrally negative Levy X and admissible dividend-strategy path D, the time-discounted Gaussian derivative coefficient evaluated at the true measurable clipped pre-jump reserve is Borel measurable on the physical time-probability product, without C2 assumptions or zero-jump assumptions. The derivative of an arbitrary real function is measurable by the pinned Mathlib measurable_deriv theorem.
-- source:
--   Apply the accepted exact original controlled clipped reserve ambient measurability theorem 55e36fd0. The derivative of an arbitrary real function is Borel measurable, with pinned Mathlib measurable_deriv. The NNReal to real physical clock coercion and exponential discount are measurable; products preserve measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_predividend_clipped_reserve_jointly_measurable_bounded
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_discounted_gaussian_coefficient_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q δ K : ℝ) (hδK : δ ≤ K) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    Measurable (fun p =>
      Real.exp (-(q * (p.1 : ℝ))) *
        (X.σ * deriv w (U p))) := by sorry
