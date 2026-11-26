-- Prove2me | Theorems.Thm_ClassicalComplexWPT_eventually_eval_weightedCoefficientSeries_eq_of_hasFPowerSeriesAt
-- name    : ClassicalComplexWPT.eventually_eval_weightedCoefficientSeries_eq_of_hasFPowerSeriesAt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:07:56.168893+00:00
-- url     : https://prove2.me/theorems/65a8fa18-d74c-5dbd-a482-4633a3c8b8a9
-- title:
--   Classical Complex WPT: eventually eval weighted Coefficient Series eq of has FPower Series At
-- statement:
--   On a sufficiently small common neighborhood, evaluating the weighted
--   moving-coefficient sequence recovers the analytic function represented by the
--   ambient formal multilinear series.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedGermEvaluation.lean#L21-L54
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedGermEvaluation.lean#L21-L54

import Definitions.Def_ClassicalComplexWPT_WeightedEvaluation
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.eventually_eval_weightedCoefficientSeries_eq_of_hasFPowerSeriesAt
    {n : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hp : HasFPowerSeriesAt f p 0) (hr0 : 0 < r)
    (hrp : (r : ℝ≥0∞) < p.radius) :
    (fun x : Ambient n ↦
      evalL1PowerSeries ((weightedCoefficientSeries p r).sum x.1)
        ((r : ℂ)⁻¹ * x.2)) =ᶠ[𝓝 0] f := by sorry
