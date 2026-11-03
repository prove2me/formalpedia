-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_prejump_valid_finite_source_mark_discounted_C1_nonpositive
-- name    : AvramDividend.Classical.avram_wave7_02_original_prejump_valid_finite_source_mark_discounted_C1_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:13:56.775898+00:00
-- url     : https://prove2.me/theorems/040d47bc-8c09-4529-ac64-2d4150222ece
-- title:
--   Original negative source jumps have nonpositive discounted finite HJB value-change sum even across ruin
-- statement:
--   For the real original spectrally negative Levy source, any finite set of actual source jump times whose original pre-source reserves are nonnegative and within the cap and whose source marks are nonpositive contributes a nonpositive discounted sum of original verification function changes. Includes source marks crossing zero or ruin, using exact pre/post source reserves and only C1 interior HJB conditions.
-- source:
--   Proved original negative source jump weak C1 all-boundary crossing theorem e76d604b and original finite-sum nonpositivity with positive discount.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_source_jump_weak_C1_value_monotone_all_crossings
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_prejump_valid_finite_source_mark_discounted_C1_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ v < 0, w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hw_grad : ∀ v : ℝ, 0 < v → ENNReal.ofReal v < C →
      1 ≤ deriv w v)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (q : ℝ)
    (S : Finset ℝ≥0)
    (hValid : ∀ t ∈ S,
      X.X t ω ≤ Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ∧
      0 ≤ x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω ∧
      ENNReal.ofReal
        (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) ≤ C) :
    (∑ t ∈ S,
      (Real.exp (-(q * (t : ℝ))) *
        (w (x + X.X t ω - D t ω) -
          w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t -
            D t ω)))) ≤ 0 := by sorry
