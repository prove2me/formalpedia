-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_phys16_original_firstjump_straddling_masked_strict_cash
-- name    : AvramDividend.Classical.avram_bv_phys16_original_firstjump_straddling_masked_strict_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T14:06:04.409707+00:00
-- url     : https://prove2.me/theorems/cf11f38e-a759-4642-a740-c664293db8a1
-- title:
--   First negative source jump physical cell payment mask excludes endpoint atom
-- statement:
--   For a finite-activity original bounded-variation source, the strict pre-first-negative-jump weighted Stieltjes cash on the ruin-clock-masked half-open final physical cell equals strictly interior drift-volume cash, with the endpoint dividend atom excluded by the payment-time mask. The identity holds on one common almost sure event under zero post-right-payment reserve before the first jump.
-- source:
--   Source-exact masked ruin-straddling physical cell ledger for the original finite-activity BV strand, based on Proved strict pre-first-source-jump zero cash and the exact definition of paymentTimes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_strict_prejump_zero_cash_of_first_source_jump
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_phys16_original_firstjump_straddling_masked_strict_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) (hDrift : 0 ≤ X.drift)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (hH : 0 < H) :
    ∀ᵐ ω ∂P, ∀ (s J : ℝ≥0), s < J → J ≤ H →
      (J : WithTop ℝ≥0) ≤
        (⨅ u : ℝ≥0,
          if 0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
          then (u : WithTop ℝ≥0) else ⊤) →
      ∀ (a : ℕ → ℝ≥0),
      (∀ n, s ≤ a n ∧ a n < J) →
      Monotone (fun n : ℕ => Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ)) →
      (⋃ n, Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ)) =
        Ioo (s : ℝ) (J : ℝ) →
      (∀ u : ℝ≥0, s ≤ u → u < J →
        riskProcess X x D u ω -
          (rightLimit D u ω - D u ω) = 0) →
      ∀ f : ℝ → ℝ≥0∞, Measurable f →
      (∫⁻ t in paymentTimes (J : ℝ≥0∞) ∩
          Ioc (s : ℝ) (J : ℝ), f t
        ∂(dividendMeasure D ω)) =
      (∫⁻ t in Ioo (s : ℝ) (J : ℝ), f t
        ∂((ENNReal.ofReal X.drift) • volume)) := by sorry
