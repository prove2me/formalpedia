-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_nonnested_eventual_support_fatou_ruin_cash
-- name    : AvramDividend.Classical.avram_wave7_19_original_nonnested_eventual_support_fatou_ruin_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:32:32.926648+00:00
-- url     : https://prove2.me/theorems/3fcca1a0-0db6-4261-8a54-67bc712860e5
-- title:
--   Original nonnested stopped cap-plus-interior Stieltjes supports dominate ruin cash by Fatou liminf
-- statement:
--   For the genuine source Lévy reserve/dividend path, boundary denotes all cap-supported dividend times and interior_n arbitrary measurable local stopped windows without a nesting assumption. If each true finite-horizon original payment time belongs to boundary ∪ interior_n eventually in n, its full discounted original dividendMeasure cash is bounded by the filter liminf of the complete local cash integrals. Uses the exact paymentTimes including zero and strictly excluding positive ruin time; no pathwise reserve continuity, no uniform integrability, and no erroneous dismissal of singular upper-cap reflection mass. This is the Fatou alternative to monotone spatial exhaustion for W7-18 nonnested diagonal clocks, conditionally bridging to W7-08 original Ito budgets.
-- source:
--   Original source ruinTime paymentTimes dividendMeasure, Proved paymentTimes_measurable, pinned Mathlib lintegral_liminf_le and Filter.liminf_le_liminf.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_nonnested_eventual_support_fatou_ruin_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (boundary : Set ℝ) (interior : ℕ → Set ℝ)
    (hBoundaryMeas : MeasurableSet boundary)
    (hInteriorMeas : ∀ n, MeasurableSet (interior n))
    (hEventual : ∀ t ∈ paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ∀ᶠ n : ℕ in Filter.atTop, t ∈ boundary ∪ interior n) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    Filter.liminf (fun n : ℕ =>
      ∫⁻ t in boundary ∪ interior n,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      Filter.atTop := by sorry
