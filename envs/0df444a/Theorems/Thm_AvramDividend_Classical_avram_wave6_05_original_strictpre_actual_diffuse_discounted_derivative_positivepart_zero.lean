-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_original_strictpre_actual_diffuse_discounted_derivative_positivepart_zero
-- name    : AvramDividend.Classical.avram_wave6_05_original_strictpre_actual_diffuse_discounted_derivative_positivepart_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:57:29.468559+00:00
-- url     : https://prove2.me/theorems/45ca6e62-59c9-4d33-af56-06b7f4f4ab2e
-- title:
--   Actual diffuse original Stieltjes dividend derivative excess has zero discounted positive part without integrability
-- statement:
--   Let ν be an atomless component of the actual original dividend Stieltjes measure, restricted to the pre-ruin closed-horizon payment set. If almost every ν-payment time has strictly positive original pre-payment reserve x+X_{s-}-D_{s+}, below cap C, and w'≥1 on that legitimate reserve interior, then the lower integral of the positive part of e^{-qs}(1-w'(x+X_{s-}-D_{s+})) against ν is exactly zero. No real integrability, absolute continuity, smooth or finite-jump dividend strategy, or restriction on q is required. Continuous and singular-continuous payment variation are both covered; simultaneous source jumps are ν-null because ν is atomless. This is precisely the diffuse dividend-control inequality for the genuine controlled Ito–Meyer decomposition.
-- source:
--   On the actual atomless dividend measure restricted to paymentTimes ∩ [0,T], the supplied local pre-payment reserve condition makes hw_grad imply 1−w'(strictPre)≤0 almost everywhere. Real.exp is positive for any real q, hence the discounted signed derivative excess is nonpositive almost everywhere and ENNReal.ofReal of it is zero. The lower-integral congruence under a.e. equality and the lower integral of zero give the exact zero positive-part statement; no integrability or finite-activity hypothesis is introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave6_05_original_strictpre_actual_diffuse_discounted_derivative_positivepart_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (q : ℝ) (w : ℝ → ℝ)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (ν : Measure ℝ) [NullSingletonClass ν]
    (hLoc : ∀ᵐ s ∂ν.restrict
      (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)),
      0 < (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
            rightLimit D s.toNNReal ω) ∧
        ENNReal.ofReal (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
            rightLimit D s.toNNReal ω) < C) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal
        (Real.exp (-(q * s)) *
          (1 - deriv w (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
            rightLimit D s.toNNReal ω))) ∂ν) = 0 := by sorry
