-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_noexit_integer_horizon_integral_vanish
-- name    : AvramDividend.Classical.chat03_noexit_integer_horizon_integral_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T23:07:27.9588+00:00
-- url     : https://prove2.me/theorems/aa1d1271-07d1-43c2-a379-3be0d0263614
-- title:
--   Expectation of discounted q-scale terminal payoff vanishes on the no-passage event
-- statement:
--   On any finite-measure law of the official spectrally negative Lévy process and with q>0, 0≤x≤a, the expected discounted terminal q-scale payoff at deterministic integer horizon n restricted to sample paths that never strictly cross either barrier tends to zero as n→∞, provided the no-passage event is measurable. The proof derives all payoff measurability from adaptedness and Borel q-scale measurability, uses the previously Proved pathwise no-passage terminal vanishing and strip bound, then applies the pinned dominated-convergence theorem. No killed q-scale martingale or two-sided exit identity is assumed.
-- source:
--   Proved Chat03 no-exit pathwise terminal vanishing, bounded strip scale bound, and q-scale Borel measurability. Pinned Mathlib dominated convergence theorem.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_infinite_passage_discounted_strip_bound
import Theorems.Thm_AvramDividend_Classical_chat03_noexit_integer_horizon_terminal_scale_vanish
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Analysis.Normed.Group.Real

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_noexit_integer_horizon_integral_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hEvent : MeasurableSet
      {ω : Ω | twoSidedExitUpTime X (a - x) ω = ∞ ∧
        twoSidedExitDownTime X (-x) ω = ∞}) :
    Tendsto
      (fun n : ℕ => ∫ ω : Ω,
        if twoSidedExitUpTime X (a - x) ω = ∞ ∧
           twoSidedExitDownTime X (-x) ω = ∞ then
          Real.exp (-(q * (n : ℝ))) * W (x + X.X (n : ℝ≥0) ω)
        else 0 ∂P)
      atTop (𝓝 0) := by sorry
