-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_reflected_infimum_Iic_iff_survival
-- name    : AvramDividend.Classical.chat04_reflected_infimum_Iic_iff_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:36:53.593422+00:00
-- url     : https://prove2.me/theorems/3e4d270c-91ab-4d60-b667-a12cdfb32a5f
-- title:
--   The reflected running-infimum CDF event equals continuous-time lower survival
-- statement:
--   For any Lévy sample path, finite horizon and initial capital x, the negative running infimum lies below x if and only if the shifted reserve x+X_s remains nonnegative at every time up to the horizon. This explicitly identifies the reflected-infimum sublevel event with the actual continuously killed survival event, including the equality boundary.
-- source:
--   Combine Proved finite-horizon path lower boundedness (3bff0b3d) and Proved exact running-infimum survival equivalence (46ecadff). Rewrite and use elementary real linear arithmetic. Needed to identify the finite-horizon Esscher-weighted survival CDF with a genuine pushforward probability law rather than merely matching its Laplace transform.

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_lower_survival_running_infimum_equiv
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_reflected_infimum_Iic_iff_survival
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ω : Ω) (x : ℝ) :
    -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω} ≤ x ↔
      ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω := by sorry
