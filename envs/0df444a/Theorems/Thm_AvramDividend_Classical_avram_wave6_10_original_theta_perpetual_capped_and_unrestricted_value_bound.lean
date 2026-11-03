-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_theta_perpetual_capped_and_unrestricted_value_bound
-- name    : AvramDividend.Classical.avram_wave6_10_original_theta_perpetual_capped_and_unrestricted_value_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:27:16.431288+00:00
-- url     : https://prove2.me/theorems/24f9b5f0-00d4-4444-bb25-6d3a0cfcdb49
-- title:
--   Original Lévy θ-budget bounds every capped and unrestricted dividend optimal value
-- statement:
--   For the actual original spectrally negative Lévy process, if θ>0 and q≥ψ(θ), every reserve cap C and the unrestricted admissible dividend optimal value have θ-scaled expected discounted value at most exp(θx). This is a source-faithful value-function supremum bridge from the accepted original-process perpetual θ cash budget and the canonical top-cap equivalence. It supplies a non-vacuous positive-capital integrability and optimal-value upper estimate relevant to downstream payout bridges; it does not replace the arbitrary C² corrected UBV HJB stochastic core.
-- source:
--   Derived directly from Proved AvramDividend.Classical.avram_wave6_08_original_theta_perpetual_expected_cash_q_ge_psi (2abbc6bc-a935-4373-95af-053049feac3c) and valueFunctionLe_top_eq_valueFunction (61c1cded-9c54-4796-9d24-f10c1d7b3100), for AvramDividend.Classical original SpectrallyNegativeLevy

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_perpetual_expected_cash_q_ge_psi
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_10_original_theta_perpetual_capped_and_unrestricted_value_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (θ : ℝ) (hθ : 0 < θ) (q : ℝ) (hq : X.ψ θ ≤ q) :
    (∀ C : ℝ≥0∞,
      ENNReal.ofReal θ * valueFunctionLe X q C x ≤
        ENNReal.ofReal (Real.exp (θ * x))) ∧
    ENNReal.ofReal θ * valueFunction X q x ≤
      ENNReal.ofReal (Real.exp (θ * x)) := by sorry
