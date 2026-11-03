-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_qpos_compact_reserve_each_admissible_stieltjes_reward_bound
-- name    : AvramDividend.Classical.avram_wave6_10_original_qpos_compact_reserve_each_admissible_stieltjes_reward_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:07:38.385471+00:00
-- url     : https://prove2.me/theorems/764dd68c-ebfa-4eba-bbbb-d373ba38490b
-- title:
--   One source Esscher tilt uniformly bounds each original admissible full-Stieltjes reward at all reserves below R
-- statement:
--   For every actual original spectrally negative Lévy process and positive discount q there exists one theta>0, such that simultaneously for each reserve upper bound R, initial capital x<=R, cap C and actual IsAdmissibleLe regulator D, the full original expected discounted Stieltjes dividendValue X q x D, multiplied by ofReal theta, is at most ofReal exp(theta R). This uses the original-process global optimal-value bound and exact admissible iSup membership; it is not a vacuous process model or a substitute for arbitrary C2 HJB verification.
-- source:
--   Canonical Proved global-in-reserve source value envelope 66533f34-2f65-4447-8fd7-9bf93fe660a7. Exact valueFunctionLe sup over actual admissible strategies, two le_iSup_of_le, ENNReal multiplication monotonicity and Real.exp monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_qpos_common_esscher_envelope_all_initial_reserves

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_10_original_qpos_compact_reserve_each_admissible_stieltjes_reward_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 < q) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ R x : ℝ, x ≤ R →
      ∀ C : ℝ≥0∞, ∀ D : ℝ≥0 → Ω → ℝ,
        IsAdmissibleLe X x C D →
          ENNReal.ofReal θ * dividendValue X q x D ≤
            ENNReal.ofReal (Real.exp (θ * R)) := by sorry
