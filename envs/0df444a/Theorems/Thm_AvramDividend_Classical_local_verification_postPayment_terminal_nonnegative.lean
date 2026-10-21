-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_postPayment_terminal_nonnegative
-- name    : AvramDividend.Classical.local_verification_postPayment_terminal_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T08:29:51.921265+00:00
-- url     : https://prove2.me/theorems/3e30828d-bef6-424c-afe5-36b4c72e7a60
-- title:
--   The HJB candidate evaluated at any post-payment controlled reserve is nonnegative
-- statement:
--   Under the exact root verification assumptions, including w(y)=0 for y<0, nonnegative w(0), the HJB derivative inequality and admissibility with ENNReal.ofReal x≤C, the terminal candidate value w(U_t+) is nonnegative for every t and every ω. The capped post-payment reserve theorem shows ENNReal.ofReal U_t+≤C at every time including t=0. If U_t+≥0, use the Proved HJB candidate lower bound w(U_t+)≥U_t++w(0)≥0. If U_t+<0, use the root condition w(y)=0 for y<0. No assumption t<ruinTime or optional stopping is needed. This is the terminal residual positivity required for the formal finite-horizon HJB upper bound.
-- source:
--   Dependency-gated from the all-times after-payment cap theorem and HJB candidate lower-bound theorem; don't publish until both are Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_candidate_lower_bound_on_cap

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_postPayment_terminal_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) :
    0 ≤ w (x + X.X t ω - rightLimit D t ω) := by sorry
