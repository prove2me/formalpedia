-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_any_cap_original_chronological_V_source_payment_jump_nonpos
-- name    : AvramDividend.Classical.avram_wave6_05_any_cap_original_chronological_V_source_payment_jump_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:16:33.588718+00:00
-- url     : https://prove2.me/theorems/39b1d2c4-41a1-4b07-86ac-fcd9cf790987
-- title:
--   Any dividend cap chronological original Lévy jump followed by right dividend payment: exact V Itô split and nonpositive cash residual
-- statement:
--   For an actual original Lévy path and any admissible left-continuous dividend strategy with any ENNReal cap, including literal zero and infinite cap, at a strictly positive strictly pre-ruin time carrying a simultaneous original source-left jump and dividend-right payment, the exact nonlinear jump correction for the cap-linear extension V splits into the source jump evaluated from the genuine strict source-prejump reserve, followed by a dividend jump evaluated at the original source-postjump reserve. The dividend cash plus V payment term is nonpositive. No local per-jump secant assumption is imposed; zero cap uses the proved affine exact value drop and positive cap uses the proved alltime cap-linear gradient secant. The derivative of V in this purely algebraic identity is formal and does not assert differentiability at cap kinks. No restriction on the total number of strategy jumps or continuous and singular-continuous variation.
-- source:
--   Source-exact chronological two-event Ito identity, positive-cap alltime V-drop, and zero-cap affine exact V-drop, all canonically Proved in pinned Mathlib.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_chronological_ito_jump_correction
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_alltime_caplinear_dividend_jump_drop
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_zero_cap_original_alltime_affine_dividend_jump_exact

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_05_any_cap_original_chronological_V_source_payment_jump_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (w V : ℝ → ℝ)
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
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (hPre : (t : ℝ≥0∞) < ruinTime X x D ω) :
    let before : ℝ :=
      x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω
    let afterSource : ℝ := x + X.X t ω - D t ω
    let afterPayment : ℝ := x + X.X t ω - rightLimit D t ω
    let sourceJump : ℝ :=
      X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t
    let paymentAtom : ℝ := rightLimit D t ω - D t ω
    (V afterPayment - V before -
        deriv V before * (sourceJump - paymentAtom) =
      (V afterSource - V before - deriv V before * sourceJump) +
        (V afterPayment - V afterSource + deriv V before * paymentAtom)) ∧
      V afterPayment - V afterSource + paymentAtom ≤ 0 := by sorry
