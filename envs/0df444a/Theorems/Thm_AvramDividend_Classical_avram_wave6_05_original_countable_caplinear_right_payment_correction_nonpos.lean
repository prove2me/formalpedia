-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_original_countable_caplinear_right_payment_correction_nonpos
-- name    : AvramDividend.Classical.avram_wave6_05_original_countable_caplinear_right_payment_correction_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:46:30.570361+00:00
-- url     : https://prove2.me/theorems/73d1bd8f-a800-4f94-a1bb-f0fbb5826858
-- title:
--   Countable discounted original chronological cap-linear dividend-jump corrections are nonpositive including time zero
-- statement:
--   For a genuinely countable family of original dividend-payment instants at zero or strictly before ruin, the absolutely summable discounted real series of chronological cap-linear V corrections δ_t + V(U_t−δ_t)−V(U_t) is nonpositive. This uses the canonically Proved all-time cap-linear source-faithful pointwise jump theorem to discharge the previously explicit hjump condition and the existing countable real series result. It retains arbitrary finite-variation strategies, simultaneous source/dividend jumps, cap and zero reserve endpoints, and the initial atom; no finite-jump restriction is imposed.
-- source:
--   The original `IsAdmissibleLe` and original Lévy `riskProcess`, accepted alltime cap-linear pointwise jump result (1a3ddaf1-be03-43cf-b243-90c0e71248d4), and accepted countable right-payment signed tsum result (dfb82109-3fc4-4efc-8c61-30724bbeac1c). Summable is explicit for real tsum semantics.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_alltime_caplinear_dividend_jump_drop
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_countable_right_payment_real_signed_sum_nonpos

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave6_05_original_countable_caplinear_right_payment_correction_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
    (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      V y = if y ≤ C.toReal then w y
        else w C.toReal + (y - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (ω : Ω)
    (A : Set ℝ≥0) (hCount : A.Countable)
    (hA : ∀ t : A,
      (t : ℝ≥0) = 0 ∨
        ((t : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω)
    (hSummable : Summable (fun t : A => Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
      ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        V (riskProcess X x D (t : ℝ≥0) ω -
          (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
        V (riskProcess X x D (t : ℝ≥0) ω)))) :
    (∑' t : A, Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
      ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        V (riskProcess X x D (t : ℝ≥0) ω -
          (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
        V (riskProcess X x D (t : ℝ≥0) ω))) ≤ 0 := by sorry
