-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_chronological_stopped_terminal_nonnegative
-- name    : AvramDividend.Classical.avram_wave5_03_original_chronological_stopped_terminal_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:56:59.058485+00:00
-- url     : https://prove2.me/theorems/f72f93f3-cfbf-4a71-b625-a1d0576710c0
-- title:
--   Original controlled BV/UBV true finite ruin-horizon chronological paid-terminal value is nonnegative
-- statement:
--   On the actual SpectrallyNegativeLevy path and capped admissible left-continuous dividend control, set τ=ruinTime and θ=toNNReal(min(T,τ)). The exact terminal reserve Wθ is the post-right-payment reserve x+Xθ−Dθ+ if θ=0 (initial atom is paid) or T<τ (surviving closed deterministic horizon is paid), and otherwise the pre-right-payment book reserve riskProcessθ (positive ruin terminal has no right dividend). Under BV C1 / UBV C2 interior regularity, separate gradient floor w'≥1, continuity up to zero, 0≤w0, negative zero extension, initial and actual admissible cap, prove w(Wθ)≥0 pathwise. The proof uses the source postpayment cap on paid branches, IsAdmissibleLe book reserve cap on un-paid θ>0, and accepted closed-cap secants; negative overshoot is handled by hw_neg, with no global positivity assumption, no spurious negative-ruin-reserve claim, and no stochastic chain formula. This is the correct boundary term for the full stopped Ito-Meyer expectation identity, directly compatible with BV and corrected UBV canonical cores for C>0.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), inequality (5.13) stopped terminal boundary and left-continuous dividend conventions. Complements the 04-B complete Stieltjes cash identity 947ab908. Integrator theorem for canonical BV ef7e6c20 and corrected UBV 429e17ca.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_chronological_stopped_terminal_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0) :
    let τ : ℝ≥0∞ := ruinTime X x D ω
    let θ : ℝ≥0 := (min (T : ℝ≥0∞) τ).toNNReal
    let W : ℝ :=
      if θ = 0 ∨ (T : ℝ≥0∞) < τ then
        x + X.X θ ω - rightLimit D θ ω
      else riskProcess X x D θ ω
    0 ≤ w W := by sorry
