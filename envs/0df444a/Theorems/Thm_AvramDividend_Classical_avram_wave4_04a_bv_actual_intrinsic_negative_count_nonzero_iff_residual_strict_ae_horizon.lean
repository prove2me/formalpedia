-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_negative_count_nonzero_iff_residual_strict_ae_horizon
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_negative_count_nonzero_iff_residual_strict_ae_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:11:34.089001+00:00
-- url     : https://prove2.me/theorems/bdf73395-27b8-40a7-aada-e18416a552ce
-- title:
--   Actual intrinsic negative Lévy jump-count occupancy equals strict source drift-residual growth uniformly on every finite BV horizon
-- statement:
--   For the actual original-space BV spectrally negative Lévy process with finite negative Lévy intensity and any fixed positive horizon T, there is one P-full event on which for all s≤t≤T the literal source-X intrinsic marked counting measure of negative nonzero jumps assigns nonzero mass to (s,t]×(-∞,0) exactly if the original drift-adjusted residual Y_u=(u:ℝ)*X.drift−X_u strictly increases from s to t. This is the uniform source-path grid-cell occupancy identity necessary to transfer the Proved source grid-binomial/Poisson scaling distribution to genuine jump count; it does not assert that full count law or a compensator.
-- source:
--   Canonical Proved d775f040 BV original residual strict interval iff an actual original X jump in the interval, on one P-full event for all s≤t≤T. Canonical Proved 4087af7c all-sample literal source intrinsic negative rectangle count zero iff every original jump mark vanishes. Classical logic and a.e. event transport give the exact nonzero-count iff strict residual increase on that same P-full event. No replacement process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_negative_count_nonzero_iff_residual_strict_ae_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iio (0 : ℝ)) ≠ 0 ↔
      (s : ℝ) * X.drift - X.X s ω <
        (t : ℝ) * X.drift - X.X t ω) := by sorry
