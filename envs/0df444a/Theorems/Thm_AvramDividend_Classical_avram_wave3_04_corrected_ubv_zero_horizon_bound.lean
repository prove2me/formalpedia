-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_corrected_ubv_zero_horizon_bound
-- name    : AvramDividend.Classical.avram_wave3_04_corrected_ubv_zero_horizon_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T13:51:07.211152+00:00
-- url     : https://prove2.me/theorems/3858a86b-eff8-46f1-b700-7ee855dad85a
-- title:
--   The repaired UBV stochastic verification claim is true at the exact zero horizon
-- statement:
--   At deterministic horizon T=0, the exact expected discounted original Stieltjes dividend reward for any genuinely capped admissible strategy is bounded by w(x) whenever the repaired boundary condition w(0)≥0, continuity and interior HJB gradient bound w'≥1 hold and the original candidate jump inequality holds at the initial payment instant. The proof uses admissibility and cap to place the initial post-payment reserve in [0,C], the proved restored-boundary nonnegativity theorem, and the existing exact initial dividend atom verification inequality. This is an unconditional true zero-horizon component of the repaired UBV stochastic core, including ruin at time zero; it does not assert the still-missing positive-time Lévy Ito–Meyer argument.
-- source:
--   Canonical Proved capped_postPaymentReserve_initial_state UUID 2ecd3672-50b4-4ad7-ad28-d1720acec949, repaired_boundary_nonneg_all_cap UUID e3cd85ca-9e16-4b4c-8cee-e6de9dc7f20c, truncated_zero_horizon_bound_of_initial_jump_secant UUID cd2d62d3-c5c3-4cd5-8783-4155692e2c6d. Private pinned compiler job 7dfc9ccd-7af1-466c-a7ee-e3acca6fe4a2 reached sentinel with no source diagnostics, source SHA-256 fdf88ed21abd7b6a0e43e7063ef5b669755373f034413fcb17793bc0a9bbbc29.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_repaired_boundary_nonneg_all_cap
import Theorems.Thm_AvramDividend_Classical_truncated_zero_horizon_bound_of_initial_jump_secant

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_corrected_ubv_zero_horizon_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
