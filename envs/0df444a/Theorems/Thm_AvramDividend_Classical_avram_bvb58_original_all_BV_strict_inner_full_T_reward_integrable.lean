-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb58_original_all_BV_strict_inner_full_T_reward_integrable
-- name    : AvramDividend.Classical.avram_bvb58_original_all_BV_strict_inner_full_T_reward_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:29:55.058075+00:00
-- url     : https://prove2.me/theorems/1debc361-6f14-481f-abdd-7bd6c98d77cf
-- title:
--   All original BV activity regimes: strict inner discounted dividends plus actual full T survival reward are integrable
-- statement:
--   For the source spectrally negative BV standing Levy process with any negative jump activity, the exact original strictly truncated positive discounted dividend cash plus its actual full physical T survival terminal candidate payoff is integrable for each n. The existing original P3 strict cash L1 and full T cash plus terminal L1 theorems yield terminal integrability by subtraction, followed by addition of truncated cash. This removes an unused infinite-jump-intensity hypothesis from the previously Proved BVA33 theorem and proves the first conjunct of BVB55 uniformly for the finite-activity original source without any pathwise compensation shortcuts.
-- source:
--   Direct generalisation of Proved original BVA33 0ba6ff9e; its accepted proof uses only Proved P3 strict cash L1 and original full T terminal-reward L1, never negative jump infinite activity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_reward_L1_nonnegative
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb58_original_all_BV_strict_inner_full_T_reward_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ n : ℕ, Integrable (F n) P := by sorry
