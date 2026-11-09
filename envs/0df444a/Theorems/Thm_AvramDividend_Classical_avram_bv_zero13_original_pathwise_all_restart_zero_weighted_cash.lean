-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_pathwise_all_restart_zero_weighted_cash
-- name    : AvramDividend.Classical.avram_bv_zero13_original_pathwise_all_restart_zero_weighted_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:06:53.845565+00:00
-- url     : https://prove2.me/theorems/33f46c30-a039-45f4-9ecd-364c79c294f5
-- title:
--   Original finite activity BV weighted zero reserve dividend cash at arbitrary pathwise restart endpoints
-- statement:
--   On one genuine original-process sample path, simultaneously for all ordered endpoints inside a fixed deterministic surviving horizon, if postpayment controlled reserve is zero throughout and no original negative source jump occurs in that interval, the actual weighted Stieltjes dividend cash equals drift-scaled Lebesgue cash. The endpoint pair may subsequently be selected based on the full adapted path, including stopping times; the theorem itself is a simultaneous pathwise event and makes no unverified random endpoint measurability claim. The left endpoint right-payment atom is excluded from the half-open interval and the final endpoint included.
-- source:
--   Root-connected original finite-cap and top-cap stopped HJB cash occupation after random adapted zero-contact restarts. Strengthens public Proved deterministic restart weighted cash 0228684b with simultaneous endpoint quantification. Uses original physical finite-jump drift-only law and public  dc73fa6f.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_postpayment_zero_Ioc_cash_eq_drift
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_zero13_original_pathwise_all_restart_zero_weighted_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hDrift : 0 ≤ X.drift)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (hH : 0 < H) :
    ∀ᵐ ω ∂P,
      ∀ (s T : ℝ≥0), s ≤ T → T ≤ H →
      (H : ℝ≥0∞) < ruinTime X x D ω →
      (∀ u : ℝ≥0, s ≤ u → u ≤ T →
        riskProcess X x D u ω -
          (rightLimit D u ω - D u ω) = 0) →
      (∀ u : ℝ≥0, u ∈ Ioc s T →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) →
      ∀ f : ℝ → ℝ≥0∞,
        (∫⁻ t in Ioc (s : ℝ) (T : ℝ), f t
          ∂(dividendMeasure D ω)) =
        (∫⁻ t in Ioc (s : ℝ) (T : ℝ), f t
          ∂((ENNReal.ofReal X.drift) • volume)) := by sorry
