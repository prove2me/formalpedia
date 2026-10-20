-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_discounted_scale_right_continuous_of_Wzero
-- name    : AvramDividend.Classical.chat03_discounted_scale_right_continuous_of_Wzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T23:10:53.296749+00:00
-- url     : https://prove2.me/theorems/c2265539-4e6a-4124-acb3-d5530a4ff876
-- title:
--   Pathwise right-continuity of discounted q-scale payoffs when W(0)=0
-- statement:
--   If W(0)=0, the official zero-extended q-scale function is continuous on all of the real line. Consequently, for every càdlàg Lévy sample path and every continuous deterministic discount, the composed discounted q-scale payoff t↦discount(t)W(x+X_t) is right-continuous at every nonnegative time, including when reserves cross zero. This is a pathwise regularity statement for later stopping-time limits and assumes no killed q-scale martingale.
-- source:
--   Already Proved chat03_scale_zero_extension_continuous_everywhere and official Lévy sample-path right-continuity, pinned Mathlib topology.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_scale_zero_extension_continuous_everywhere
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Algebra.Monoid.Defs

open MeasureTheory Filter Set Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_discounted_scale_right_continuous_of_Wzero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (discount : ℝ≥0 → ℝ) (hdiscount : Continuous discount)
    (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt
      (fun s : ℝ≥0 => discount s * W (x + X.X s ω))
      (Set.Ici t) t := by sorry
