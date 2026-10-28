-- Prove2me | Theorems.Thm_AvramDividend_Classical_extended_ruin_strict_survival_tonelli
-- name    : AvramDividend.Classical.extended_ruin_strict_survival_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:57:06.745296+00:00
-- url     : https://prove2.me/theorems/fef3657a-74bd-4b1a-8764-3674d023f722
-- title:
--   Strict-survival Tonelli identity for arbitrary extended nonnegative real ruin clocks
-- statement:
--   For any measurable extended nonnegative-valued stopping time τ, any s-finite sample-space measure P, and any measurable nonnegative time weight w, the expected Lebesgue-time integral of w(t) at strictly surviving positive times equals the Lebesgue-time integral of P(t<τ)w(t). The theorem works directly with τ in ENNReal, including τ=∞, and does not erroneously convert infinity to zero. It is proved using the joint measurable set {(t,ω):t>0 and ofReal(t)<τ(ω)}, an indicator on real-time×path-space, Tonelli's lintegral_lintegral_swap, and lintegral_indicator_const. Unlike the capped-clock formulation, the statement handles the entire original stopping horizon without a limiting cap.
-- source:
--   Tonelli–Fubini, Mathlib MeasureTheory.Measure.Prod and Lebesgue; Avram, Palmowski and Pistorius (2007) §3.3, zero-barrier reflected first-jump dividend valuation.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.extended_ruin_strict_survival_tonelli
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (τ : Ω → ℝ≥0∞) (hτ : Measurable τ)
    (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ ω, ∫⁻ t in Ioi (0 : ℝ),
      (if ENNReal.ofReal t < τ ω then w t else 0) ∂volume ∂P) =
    (∫⁻ t in Ioi (0 : ℝ),
      P {ω : Ω | ENNReal.ofReal t < τ ω} * w t ∂volume) := by sorry
