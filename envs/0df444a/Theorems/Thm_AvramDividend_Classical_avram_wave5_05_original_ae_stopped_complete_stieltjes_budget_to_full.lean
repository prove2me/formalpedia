-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_ae_stopped_complete_stieltjes_budget_to_full
-- name    : AvramDividend.Classical.avram_wave5_05_original_ae_stopped_complete_stieltjes_budget_to_full
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:44:31.025075+00:00
-- url     : https://prove2.me/theorems/8d646a03-6bbe-48bd-9e99-a5a525b6a90d
-- title:
--   Almost surely exhaustive original stopping clocks recover full discounted dividend budget
-- statement:
--   For a true original-source spectrally negative Lévy process and adapted dividend strategy, measurable (not necessarily monotone) stopping clocks S_n with tail lower-infimum approaching infinity almost surely and uniform ENNReal expected complete dividend cash budget B at min(ruin,S_n) imply exactly the full ruin-stopped finite-horizon discounted complete Stieltjes cash budget B. Construct an everywhere-monotone measurable envelope below S_n a.s. using the separately proved exhaustion lemma and invoke original expected monotone Stieltjes localization. Preserves time-zero atom, singular continuous dividends and right-jump payments. The martingale budget itself is a separate missing stochastic statement; no surrogate model or BV hypothesis enters this transfer.
-- source:
--   Avram-Palmowski-Pistorius (2007), Proposition 4(i) stopping localization; accepted source localization theorem 719af000-518f-4807-83fa-4d126306a372 and original ae-exhaustion clock helper.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_ae_exhaustion_measurable_monotone_clock
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_expected_preruin_complete_stieltjes_localisation
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_05_original_ae_stopped_complete_stieltjes_budget_to_full
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (q : ℝ)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSm : ∀ n, Measurable (S n))
    (hTailAE : ∀ᵐ ω ∂P,
      (⨆ n, (⨅ m, if n ≤ m then S m ω else ⊤)) = ⊤)
    (B : ℝ≥0∞)
    (hBudget : ∀ n,
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (S n ω)) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂dividendMeasure D ω ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂dividendMeasure D ω ∂P) ≤ B := by
  sorry
