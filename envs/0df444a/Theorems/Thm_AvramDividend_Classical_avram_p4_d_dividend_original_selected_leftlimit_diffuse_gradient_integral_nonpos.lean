-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_selected_leftlimit_diffuse_gradient_integral_nonpos
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_selected_leftlimit_diffuse_gradient_integral_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:00:32.19511+00:00
-- url     : https://prove2.me/theorems/fa6f235f-2f50-4bc1-bd2d-f9f244f5f181
-- title:
--   The true source left-limit/right-dividend-limit diffuse signed Stieltjes gradient integral is nonpositive on every justified interior selected region
-- statement:
--   For the original Lévy process, a path-dependent atomless Stieltjes component and a selected measurable payment region, the exact original diffuse signed control correction at x + leftLim X - rightLimit D is nonpositive whenever the actual component measure sees only strictly interior reserve states, the original derivative lower bound holds there, and the real signed integrand is integrable on that region. This is the source convention of the stopped Itô–Meyer diffuse term, including singular-continuous dividend mass on the selected region; the cap and lower-boundary contact masses are explicitly outside the supported interior claim.
-- source:
--   Original stopped full-Stieltjes diffuse source convention 48e15f54-f747-48fb-9f15-9f02ae7a538b and selected path-dependent atomless reserve identification a14bf58b-7618-46d8-8305-425cfaa67b49. Pinned Mathlib integral_nonpos_of_ae and Real.exp_pos.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_selected_leftlimit_diffuse_gradient_integral_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (ν : Measure ℝ) [NullSingletonClass ν]
    (A : Set ℝ) (hA : MeasurableSet A)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hregion : ∀ᵐ s ∂ν.restrict A,
      0 < (x +
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω) ∧ ENNReal.ofReal (x +
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω) < C)
    (hInt : IntegrableOn (fun s : ℝ => Real.exp (-(q * s)) *
      (1 - deriv w (x +
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω))) A ν) :
    (∫ s in A, Real.exp (-(q * s)) *
      (1 - deriv w (x +
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω)) ∂ν) ≤ 0 := by sorry
