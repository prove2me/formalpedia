-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_natural_ruin_cofinal_local_budget_to_cash
-- name    : AvramDividend.Classical.avram_sweep16_original_natural_ruin_cofinal_local_budget_to_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:18:29.588358+00:00
-- url     : https://prove2.me/theorems/f0418428-49ff-4177-8c6c-248ebce21e9f
-- title:
--   Natural original ruin-clock discounted dividend budget from cofinal physical localisation budgets, preserving complete Stieltjes atoms
-- statement:
--   For the unchanged original physical X,D, natural finite ruin clock and an increasing right-continuous stopping localisation S cofinal to top, assume precisely the expected closed physical Stieltjes cash budget at each localised clock. The eventual exact equality at each path and original random-clock measurability imply the required Fatou liminf and measurable cash hypotheses. Apply the already-Proved source-exact ENNReal Fatou inequality to conclude the natural ruin-clock cash upper bound with no uniform integrability or global mean-zero inference. The remaining stochastic obligation is the genuine hBudget at finite localisers.
-- source:
--   SWEEP16 original stopped-clock source; independently Proved original clock eventual cash equality fd7f8c61, local cash measurability a056bf2c, and original no-UI Fatou da912121.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_natural_clock_cofinal_stieltjes_cash_eventually_exact
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_natural_ruin_cofinal_local_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_ruin_clock_localized_cash_fatou_no_ui
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_sweep16_original_natural_ruin_cofinal_local_budget_to_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (n : ℕ) (w : ℝ → ℝ)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ k, IsStoppingTime 𝓕.rightCont (S k))
    (hSmono : ∀ ω, Monotone (fun k => S k ω))
    (hSsup : ∀ ω, (⨆ k : ℕ, S k ω) = ⊤)
    (hBudget : ∀ k : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (((min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Iic (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ)),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    ENNReal.ofReal (w x) := by sorry
