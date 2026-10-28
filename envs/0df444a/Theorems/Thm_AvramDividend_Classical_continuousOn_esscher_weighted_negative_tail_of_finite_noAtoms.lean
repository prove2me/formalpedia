-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousOn_esscher_weighted_negative_tail_of_finite_noAtoms
-- name    : AvramDividend.Classical.continuousOn_esscher_weighted_negative_tail_of_finite_noAtoms
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:32:55.530749+00:00
-- url     : https://prove2.me/theorems/f0f4c508-53ea-4672-b231-e0ef9bcee89f
-- title:
--   Continuity of locally finite Esscher-weighted negative jump tails
-- statement:
--   For an atomless Lévy jump measure, the exponentially Esscher-weighted negative jump tail is continuous as the positive jump-size threshold varies, provided weighted tails are finite away from zero. This removes a signed-measure continuity step when constructing the bounded-variation renewal kernel used for C1 scale regularity and cstar finiteness.
-- source:
--   General atomless cumulative continuity, already Proved in continuousOn_measureReal_Iic_negative_of_finite_noAtoms, and absolute continuity of density-weighted measures.

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_continuousOn_measureReal_Iic_negative_of_finite_noAtoms
open AvramDividend.Classical MeasureTheory Set Topology
open scoped ENNReal

theorem AvramDividend.Classical.continuousOn_esscher_weighted_negative_tail_of_finite_noAtoms
    (ν : Measure ℝ) [NullSingletonClass ν] (φ : ℝ)
    (hfinite : ∀ a : ℝ, a < 0 →
      (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y)))) (Iic a) ≠ ⊤) :
    ContinuousOn (fun r : ℝ =>
      (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y)))).real (Iic (-r)))
      (Ioi (0 : ℝ)) := by sorry
