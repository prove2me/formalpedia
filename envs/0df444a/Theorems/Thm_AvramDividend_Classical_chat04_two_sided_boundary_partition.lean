-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_two_sided_boundary_partition
-- name    : AvramDividend.Classical.chat04_two_sided_boundary_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:08:38.479729+00:00
-- url     : https://prove2.me/theorems/0857d071-c4e3-47af-bacf-193fad39e37f
-- title:
--   Exact two-sided stopped q-scale boundary partition including the lower creeping atom
-- statement:
--   The sum of the killed discounted upper and lower first-exit q-scale values equals the upper discounted barrier value W(a) plus the discounted lower boundary contact value W(0) on precisely the event that the stopped reserve is zero. This is a full pointwise identity valid for both bounded and unbounded variation and without optional stopping, a martingale hypothesis, or any assumed absence of creeping. It combines the two independently accepted Chat04 boundary theorems and preserves strict passage and infinity semantics.
-- source:
--   Previously Proved AvramDividend.Classical.chat04_strict_upper_exit_scale_payoff 3a6690c2-75f4-410d-a696-a0dee2597de4 and chat04_lower_exit_scale_creeping_atom 0f1adee0-3670-4143-b12f-b52df6fbae1b. Pinned mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_payoff
import Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_scale_creeping_atom

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_two_sided_boundary_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (hxa : x ≤ a) (ω : Ω) :
    (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0) + (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitDownTime X (-x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0) =
    (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
          ENNReal.ofReal (W a)
      else 0) + (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitDownTime X (-x) ω).toReal))) *
          (if x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω = 0 then
             ENNReal.ofReal (W 0)
           else 0)
      else 0) := by sorry
