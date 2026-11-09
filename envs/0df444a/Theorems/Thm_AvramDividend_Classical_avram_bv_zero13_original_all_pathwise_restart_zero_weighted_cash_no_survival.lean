-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_all_pathwise_restart_zero_weighted_cash_no_survival
-- name    : AvramDividend.Classical.avram_bv_zero13_original_all_pathwise_restart_zero_weighted_cash_no_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:19:31.264453+00:00
-- url     : https://prove2.me/theorems/bc78efba-a3bb-4269-ab9a-192e4303b30a
-- title:
--   Original BV weighted zero reserve cash at every pathwise interval without requiring the enclosing horizon to survive
-- statement:
--   The original finite activity BV drift-only sample-path identity holds simultaneously on every interval of a fixed deterministic clock. For arbitrary original adapted admissible dividends, if the postpayment reserve is identically zero and the original physical source has no negative jump on the selected half-open subinterval, the full weighted physical Stieltjes cash agrees with drift-scaled Lebesgue cash. No survival assumption is made at the enclosing deterministic clock, so a pathwise subinterval may be chosen strictly before ruin even if ruin occurs before that enclosing clock. The left-endpoint right-payment atom is excluded and the final endpoint included. This is the corrected first-negative-jump-ready strengthening of the earlier surviving-horizon helper.
-- source:
--   Root-connected missing interface for finite-cap and top-cap original BV strict pre-ruin cash at pathwise stopping or first negative jump approximating endpoints. Proved physical nojump drift identity 2a0cae7c and original D cash identity dc73fa6f; no auxiliary jump source.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_postpayment_zero_Ioc_cash_eq_drift
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_zero13_original_all_pathwise_restart_zero_weighted_cash_no_survival
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
