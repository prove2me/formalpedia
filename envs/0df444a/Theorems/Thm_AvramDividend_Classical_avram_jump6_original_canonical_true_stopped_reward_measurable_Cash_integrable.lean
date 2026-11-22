-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_original_canonical_true_stopped_reward_measurable_Cash_integrable
-- name    : AvramDividend.Classical.avram_jump6_original_canonical_true_stopped_reward_measurable_Cash_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T19:51:28.386827+00:00
-- url     : https://prove2.me/theorems/48783265-ab89-4afd-8565-94268c6b769a
-- title:
--   Exact original ruin-clipped stopped terminal measurability and inclusive physical dividend cash L1 transfer to arbitrary canonical variables
-- statement:
--   For an arbitrary source-faithful choice of W, Cash and Term at the original integer-horizon ruin-clipped stopping time, prove that the stopped discounted terminal is almost everywhere strongly measurable and the exact inclusive pre-ruin Stieltjes cash is integrable. The existing Proved source witness theorem establishes existence of a canonical triple with these properties. As all three components are uniquely determined pointwise by the exact original identities, the properties transfer to any equally defined variables. This removes a previously extra terminal measurability premise in the finite-activity infinite-cap HJB expected-budget source, without changing the stopped convention or requiring any Ito–Meyer inequality.
-- source:
--   Proved avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses 4a50bbff-06c2-4bbb-9102-1cd6b925d63d. Root finiteactivity positive event budget 15815eff contains exactly these source equations and clock assumptions, but currently assumes Cash L1 only; topcap source 7d0ba210 additionally asks Term ae measurable, now derivable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_original_canonical_true_stopped_reward_measurable_Cash_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    AEStronglyMeasurable Term P ∧ Integrable Cash P := by sorry
