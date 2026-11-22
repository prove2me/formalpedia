-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_finiteactivity_topcap_HJB_actual_stopped_full_reward_L1
-- name    : AvramDividend.Classical.avram_jump6_finiteactivity_topcap_HJB_actual_stopped_full_reward_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T19:48:19.570049+00:00
-- url     : https://prove2.me/theorems/7d0ba210-39b2-4351-87be-76da474c7b1f
-- title:
--   Infinite-cap finite-activity original HJB growth implies L1 post-right-dividend stopped terminal and entire reward
-- statement:
--   For the original finite-activity Lévy process with unbounded variation and arbitrary admissible dividend strategy, under the source's HJB maximum equation at infinite cap and its standard almost-everywhere measurable stopped terminal, prove the stopped terminal is L1 and hence full stopped terminal-plus-dividend cash is L1, without an artificial finite reserve cap. The proof obtains σ>0 from finite activity, both generator≤0 and gradient≥1 from the HJB maximum equation, the source's exponential spatial growth envelope for w, and a Proved original bounded-stop exponential moment. Includes measurability of the positive-clock event in the right-continuous initial filtration. This closes the infinite-cap integrability component of the finite-activity original positive-clock budget, leaving the actual expected Ito–Meyer inequality.
-- source:
--   Open original finite-activity expected stopped budget 15815eff, Proved topcap HJB exponential envelope b63a7504, Proved bounded-stop terminal L1 for exponential candidate envelope 29054c1d, Proved nonnegative exact source terminal f6fef241, Proved bounded physical ruin clock edebe535, and Proved initial event measurable bce62e25.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_finiteactivity_UBV_gaussian_sigma_positive
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_finiteactivity_UBV_topcap_HJB_exponential_growth
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_terminal_L1_of_bounded_exp_growth_any_q
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_finiteactivity_topcap_HJB_actual_stopped_full_reward_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxpos : 0 < x)
    (k : ℕ) (hk : 0 < k)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (k : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hCashI : Integrable Cash P)
    (hTop : C = ⊤)
    (hTermMeas : AEStronglyMeasurable Term P) :
    (0 < X.σ) ∧
    Integrable Term P ∧
    Integrable (fun ω => Term ω + Cash ω) P ∧
    MeasurableSet[𝓕.rightCont 0] {ω : Ω | τ ω ≠ 0} := by sorry
