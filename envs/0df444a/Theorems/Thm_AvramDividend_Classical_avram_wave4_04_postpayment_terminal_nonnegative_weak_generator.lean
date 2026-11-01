-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_postpayment_terminal_nonnegative_weak_generator
-- name    : AvramDividend.Classical.avram_wave4_04_postpayment_terminal_nonnegative_weak_generator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:04:27.833986+00:00
-- url     : https://prove2.me/theorems/567c1077-6ef8-46dd-939d-568ef6ba61fe
-- title:
--   Original controlled post-payment candidate is nonnegative under corrected boundary and interior gradient alone
-- statement:
--   For the actual controlled post-payment reserve x+X_t-D_t^+ in the same sample and filtration, the corrected boundary sign w(0)≥0, continuity on nonnegative reserves, local C² below cap, interior derivative lower bound w'≥1, cap-admissibility and zero extension w(y)=0 below zero force w to be nonnegative at every post-payment reserve, including ruin overshoots and cap contact. No full max-HJB equality, source semimartingale decomposition or compensation is assumed. This strengthens the older full-HJB terminal theorem and supplies the terminal sign for the corrected finite-horizon verification.
-- source:
--   Previously remotely elaborated exact main-target subproof hPostTerminalNonneg; Proved capped_postPaymentReserve_ofReal_le_cap and avram_wave3_04_ubv_HJB_candidate_dominates_initial_capital; no stochastic lemma or circular verification theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_HJB_candidate_dominates_initial_capital

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_04_postpayment_terminal_nonnegative_weak_generator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) :
    0 ≤ w (x + X.X t ω - rightLimit D t ω) := by sorry
