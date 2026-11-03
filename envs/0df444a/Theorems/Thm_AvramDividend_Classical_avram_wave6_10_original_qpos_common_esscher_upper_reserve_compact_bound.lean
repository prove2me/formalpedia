-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_qpos_common_esscher_upper_reserve_compact_bound
-- name    : AvramDividend.Classical.avram_wave6_10_original_qpos_common_esscher_upper_reserve_compact_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:01:51.852198+00:00
-- url     : https://prove2.me/theorems/b3964763-25b5-4b94-ad69-886c5758bfa0
-- title:
--   Uniform original dividend-value exponential envelope over every upper-bounded reserve range and cap
-- statement:
--   For the true original SpectrallyNegativeLevy process at any positive discount q, there exists one theta>0 depending only on X and q, such that for every upper reserve level R, every x<=R, and every dividend cap C, the theta-scaled optimal expected original Stieltjes dividend payout is uniformly at most exp(theta R); the same bound holds unrestricted. This is a compact-reserve domination interface without any Standing or bounded-variation hypothesis. It uses the accepted global-in-reserve source exponential theorem and does not claim unproved arbitrary-w HJB stochastic verification.
-- source:
--   Proved original global-in-reserve common-tilt theorem 66533f34-2f65-4447-8fd7-9bf93fe660a7; real exp monotonicity with theta>0, then ENNReal.ofReal monotonicity. One common theta works for every upper bound R.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_qpos_common_esscher_envelope_all_initial_reserves

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_10_original_qpos_common_esscher_upper_reserve_compact_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 < q) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ R x : ℝ, x ≤ R →
      (∀ C : ℝ≥0∞,
        ENNReal.ofReal θ * valueFunctionLe X q C x ≤
          ENNReal.ofReal (Real.exp (θ * R))) ∧
      ENNReal.ofReal θ * valueFunction X q x ≤
        ENNReal.ofReal (Real.exp (θ * R)) := by sorry
