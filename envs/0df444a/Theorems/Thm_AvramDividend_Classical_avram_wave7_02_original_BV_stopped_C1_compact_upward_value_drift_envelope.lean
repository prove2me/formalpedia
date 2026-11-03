-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_stopped_C1_compact_upward_value_drift_envelope
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_stopped_C1_compact_upward_value_drift_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:47:22.659203+00:00
-- url     : https://prove2.me/theorems/ff5e7a18-eb69-4fe9-b3d4-0430206be855
-- title:
--   True original stopped BV C1 postpayment value upward increments bounded by local physical drift
-- statement:
--   For the true original bounded-variation spectrally negative Levy source and monotone right-dividend strategy on one common almost-sure event, at any pair of ordered times whose literal postpayment controlled reserves lie in a positive-cap compact strip, the C1 HJB candidate value can increase by at most the deterministic elapsed time times the physical drift times its local Lipschitz ceiling. Downward negative jumps or dividend jumps only decrease the value because the canonical gradient is at least one; upward motion is limited by the original BV physical source drift. This is a source-specific pathwise stopped C1 chain inequality including singular-continuous loss and simultaneous right payments. Compact-band assumptions do not assert control at ruin crossing or cap contact outside the band.
-- source:
--   Accepted original BV controlled reserve pathwise increment bound 6c45ed32, original full-cap weak C1 secant 2ba5cc4f, compact Lipschitz control.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_stopped_C1_compact_upward_value_drift_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (a b L : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hbC : ENNReal.ofReal b ≤ C)
    (hL : 0 ≤ L) (hd : 0 ≤ X.drift)
    (hLip : ∀ y ∈ Icc a b, ∀ z ∈ Icc a b,
      |w y - w z| ≤ L * |y - z|) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      x + X.X s ω - rightLimit D s ω ∈ Icc a b →
      x + X.X t ω - rightLimit D t ω ∈ Icc a b →
      w (x + X.X t ω - rightLimit D t ω) -
        w (x + X.X s ω - rightLimit D s ω) ≤
          L * (((t : ℝ) - (s : ℝ)) * X.drift) := by sorry
