-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_qpos_common_esscher_every_real_horizon_each_admissible_cash_bound
-- name    : AvramDividend.Classical.avram_wave6_10_original_qpos_common_esscher_every_real_horizon_each_admissible_cash_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:42:14.639205+00:00
-- url     : https://prove2.me/theorems/523fa9d2-6313-4b1d-8352-8c0c16930150
-- title:
--   One original Esscher parameter controls every finite-real-horizon admissible Stieltjes payout uniformly in reserve and cap
-- statement:
--   For any original SpectrallyNegativeLevy process and positive discount q, there is a single positive exponential parameter theta depending only on the source and q. Simultaneously for every reserve ceiling R, initial capital x<=R, cap C, admissible original dividend regulator D and real horizon T (including zero), the theta-scaled exact original expected discounted Stieltjes dividend payment up to T and ruin is at most ofReal exp(theta R). This directly links finite-real-time payoff to an already Proved full-value envelope on the original process without extra Ito axioms or altered model.
-- source:
--   Canonical Proved source per-admissible-strategy full-Stieltjes reward bound 764dd68c-ebfa-4eba-bbbb-d373ba38490b, exact source definition dividendValue, set inclusion into paymentTimes, and Mathlib ENNReal lintegral_mono_set/lintegral_mono. Bridges exact real-horizon local payout to a uniform full-horizon envelope.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_qpos_compact_reserve_each_admissible_stieltjes_reward_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_10_original_qpos_common_esscher_every_real_horizon_each_admissible_cash_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 < q) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ R x : ℝ, x ≤ R →
      ∀ C : ℝ≥0∞, ∀ D : ℝ≥0 → Ω → ℝ,
        IsAdmissibleLe X x C D → ∀ T : ℝ,
          ENNReal.ofReal θ *
            (∫⁻ ω, ∫⁻ t in
              paymentTimes (ruinTime X x D ω) ∩ Iic T,
              ENNReal.ofReal (Real.exp (-(q * t)))
                ∂(dividendMeasure D ω) ∂P) ≤
            ENNReal.ofReal (Real.exp (θ * R)) := by sorry
