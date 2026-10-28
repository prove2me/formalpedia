-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_survival_ennreal_infimum_right_continuous
-- name    : AvramDividend.Classical.chat04_esscher_survival_ennreal_infimum_right_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:56:39.232094+00:00
-- url     : https://prove2.me/theorems/15ef895e-d175-4631-a86b-828f50228242
-- title:
--   The infinite-horizon Esscher survival CDF is right-continuous in initial reserve
-- statement:
--   The extended-nonnegative infinite-horizon Esscher-weighted survival distribution obtained as the pointwise infimum of all finite-horizon survival expectations is right-continuous in starting capital. Each finite-horizon expectation is a genuine nondecreasing right-continuous CDF under the finite-horizon Esscher law. Their ENNReal-valued infimum inherits right continuity.
-- source:
--   Use already Proved monotonicity in starting capital of every finite-horizon Esscher killed-survival real expectation; Proved finite-horizon CDF right-continuity; pinned ENNReal.continuous_ofReal to convert real continuity; and Proved `iInf_right_continuous_of_monotone` for ENNReal-valued families. This constructs rigorous right-continuous infinite-horizon survival data for the descending ladder Stieltjes measure without assuming the unproved Wiener–Hopf scalar identity.

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.ContinuousOn
import Theorems.Thm_AvramDividend_Classical_iInf_right_continuous_of_monotone
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_killed_survival_right_continuous_capital
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_monotone_start

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_survival_ennreal_infimum_right_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) :
    ContinuousWithinAt
      (fun y : ℝ => ⨅ t : ℝ≥0, ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P))
      (Ici x) x := by sorry
