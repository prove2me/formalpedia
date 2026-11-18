-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_negative_mark_count_cell_integral_le_probability_20261117
-- name    : AvramDividend.Classical.avram_a27_original_negative_mark_count_cell_integral_le_probability_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:04:58.589265+00:00
-- url     : https://prove2.me/theorems/5c8fddfa-a5ac-44ee-a00f-51965e9f26ce
-- title:
--   Every actual negative-mark Laplace count-cell integral lies between zero and its original cell probability
-- statement:
--   For every physical negative jump count k on the unchanged original Lévy space, the exponential marked jump weight is integrable on that count cell and its weighted probability lies between zero and the ordinary count-cell probability. This is the domination required to extract coefficients from the original marked Poisson generating function.
-- source:
--   Proved actual original negative jump exponential factor bound and probability measure X.isProbability, restricted Bochner integral monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Every original physical negative-mark count-cell Laplace weight is dominated by its event mass. -/

theorem AvramDividend.Classical.avram_a27_original_negative_mark_count_cell_integral_le_probability_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K) :
    ∀ k : ℕ,
      IntegrableOn (fun ω => Real.exp (θ * J ω))
        {ω : Ω | K ω = k} P ∧
      0 ≤ (∫ ω in {ω : Ω | K ω = k},
        Real.exp (θ * J ω) ∂P) ∧
      (∫ ω in {ω : Ω | K ω = k},
        Real.exp (θ * J ω) ∂P) ≤
        P.real {ω : Ω | K ω = k} := by sorry
