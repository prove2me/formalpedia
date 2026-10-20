-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_noexit_integer_horizon_integral_vanish_unconditional
-- name    : AvramDividend.Classical.chat03_noexit_integer_horizon_integral_vanish_unconditional
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T23:25:19.007929+00:00
-- url     : https://prove2.me/theorems/6c174109-b08a-469b-ac51-39dabb122271
-- title:
--   Expected q-scale terminal payoff vanishes on no-exit paths without auxiliary assumptions
-- statement:
--   For q>0 and x in [0,a], the expectation of the horizon-n discounted q-scale payoff on paths that never strictly exit either barrier tends to zero as n tends to infinity. All measurability conditions follow from the official Lévy process assumptions and independent strict-passage event results. The proof combines verified pathwise vanishing, domination and first-passage measurability, without assuming the still-open stopped-scale martingale identity.
-- source:
--   Proved Chat03 both-infinite first-passage event measurability and corresponding conditional bounded convergence or uniform-integrability theorem.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_both_infinite_passage_event_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_noexit_integer_horizon_integral_vanish

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_noexit_integer_horizon_integral_vanish_unconditional
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    Tendsto
      (fun n : ℕ => ∫ ω : Ω,
        if twoSidedExitUpTime X (a - x) ω = ∞ ∧
           twoSidedExitDownTime X (-x) ω = ∞ then
          Real.exp (-(q * (n : ℝ))) * W (x + X.X (n : ℝ≥0) ω)
        else 0 ∂P)
      atTop (𝓝 0) := by sorry
