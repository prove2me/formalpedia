-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_legacy_bv_universal_bound_formally_refuted_conditionally
-- name    : AvramDividend.Classical.avram_wave7_09_legacy_bv_universal_bound_formally_refuted_conditionally
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:36:06.838619+00:00
-- url     : https://prove2.me/theorems/60be6ba9-7cde-4e7b-9f26-889291c0bce7
-- title:
--   Exact conditional formal refutation of the legacy BV universal zero-cap stochastic bound
-- statement:
--   For every fixed original spectrally negative Lévy process satisfying Standing and BoundedVariation, every positive discount q and strictly positive initial reserve x, the universal closure of all analytical and stochastic premises and the conclusion of historical BV parent 65617e0a is formally false. This refutation is conditional on the original process X and does not independently construct any process witness. It uses the Proved original-process zero-cap witness theorem c4bc3559, and distinguishes logical incompatibility from an unconditional Disproved platform status.
-- source:
--   Original X/P/filtration, paymentTimes, ruinTime, dividendMeasure; Proved c4bc3559 only. No imported Open target.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_legacy_bv_universal_bound_formally_refuted_conditionally
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q x : ℝ) (hq : 0 < q) (hx : 0 < x) :
    ¬ (∀ (w : ℝ → ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (T : ℝ),
      ContinuousOn w (Ici 0) →
      (∀ y < 0, w y = 0) →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} →
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) →
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) →
      IsAdmissibleLe X x C D →
      (∀ ω (t : ℝ≥0), 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ w (riskProcess X x D t ω)) →
      0 ≤ T →
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x))  := by sorry
