-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gclose16_original_stopping_right_neighbourhood_strict_postpayment_preruin
-- name    : AvramDividend.Classical.avram_gclose16_original_stopping_right_neighbourhood_strict_postpayment_preruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:32:44.807134+00:00
-- url     : https://prove2.me/theorems/676c1478-74cf-4c49-b34b-407dc4a04987
-- title:
--   Strict original postpayment reserve persists immediately right of any genuine pre-ruin stopping clock
-- statement:
--   At any original right-continuous-filtration stopping clock strictly before ruin, the original post-dividend reserve remains strictly positive throughout some right neighbourhood of that stopping time, almost surely. This follows from the Proved single stopping strict-solvency theorem and the Proved pathwise right-continuity of the unchanged controlled reserve. It is a local original-process input for sampled lower-exit cofinality and does not assert uniform strict positivity on every compact prefix.
-- source:
--   Proved 0e9f7014 gives strict postpayment solvency at the stopping clock; Proved a2202506 gives right continuity in the physical reserve. Transfer membership in the real open half-line through the continuous-within filter.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gclose16_original_rightcont_stopping_strict_postpayment_preruin
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_postrightpayment_reserve_pathwise_rightcontinuous

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gclose16_original_stopping_right_neighbourhood_strict_postpayment_preruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P,
      (τ ω : ℝ≥0∞) < ruinTime X x D ω →
      ∀ᶠ s in 𝓝[Set.Ici (τ ω)] (τ ω),
        0 < x + X.X s ω - rightLimit D s ω := by sorry
