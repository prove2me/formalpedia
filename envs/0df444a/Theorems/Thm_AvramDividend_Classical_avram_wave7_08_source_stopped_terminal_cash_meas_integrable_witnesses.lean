-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
-- name    : AvramDividend.Classical.avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:19:24.448026+00:00
-- url     : https://prove2.me/theorems/4a50bbff-06c2-4bbb-9102-1cd6b925d63d
-- title:
--   Original-process stopped terminal and Stieltjes cash witnesses with measurable terminal and integrable cash
-- statement:
--   For the actual finite stopped original Lévy process and canonical post-dividend reserve, construct W and discounted original Stieltjes Cash and terminal reward Term, prove terminal AEStronglyMeasurable and real Cash integrable under original admissibility. Uses Proved exact source terminal measurability, source stopped Cash integrability, and exact bounded ruin clock. This closes the deterministic/measure-theoretic witness component of source Itô, leaving original martingales and one-sided inequality.
-- source:
--   Sub-claim of exact W7-08 stochastic residual child 750ad13b. All variables use the parent's exact original Ω/P/X/filtration, ruinTime, rightLimit, paymentTimes, dividendMeasure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∃ W Cash Term : Ω → ℝ,
      (∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
        then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
        else riskProcess X x D (τ ω) ω) ∧
      (∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) ∧
      (∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) ∧
      AEStronglyMeasurable Term P ∧ Integrable Cash P := by sorry
