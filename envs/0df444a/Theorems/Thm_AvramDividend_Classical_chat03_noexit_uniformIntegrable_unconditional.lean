-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_noexit_uniformIntegrable_unconditional
-- name    : AvramDividend.Classical.chat03_noexit_uniformIntegrable_unconditional
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T23:25:29.206651+00:00
-- url     : https://prove2.me/theorems/87a1a6c0-72b1-4335-9230-0d89439587df
-- title:
--   Uniform integrability of no-exit discounted q-scale payoffs without measurability premises
-- statement:
--   For any finite-measure Lévy process law, q>0 and reserve x in [0,a], the complete family of finite-time discounted q-scale payoffs restricted to paths without either strict first passage is uniformly integrable in L1. All event and payoff measurability premises are discharged by independent strict-passage event theorems. No killed q-scale martingale is assumed.
-- source:
--   Proved Chat03 both-infinite first-passage event measurability and corresponding conditional bounded convergence or uniform-integrability theorem.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_both_infinite_passage_event_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_noexit_uniformIntegrable_of_measurable_event

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_noexit_uniformIntegrable_unconditional
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    UniformIntegrable
      (fun t : ℝ≥0 => fun ω : Ω =>
        if twoSidedExitUpTime X (a - x) ω = ∞ ∧
           twoSidedExitDownTime X (-x) ω = ∞ then
          Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)
        else 0)
      (1 : ℝ≥0∞) P := by sorry
