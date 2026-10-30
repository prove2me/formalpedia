-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_bv_drawdown_zero_atom_measure
-- name    : AvramDividend.Classical.avram_ws01b_actual_bv_drawdown_zero_atom_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:27:35.191065+00:00
-- url     : https://prove2.me/theorems/8b29d17a-e307-4e6c-8b39-bfe215486391
-- title:
--   True original-law BV exponential-clock drawdown atom as ENNReal measure mass
-- statement:
--   For the genuine original spectrally negative bounded-variation Lévy process observed at an independent Exp(R) clock, the pushforward terminal drawdown distribution assigns mass R/(Φ(R)d) to zero. The equality is in extended nonnegative measures and follows from the canonically proved real original-clock drawdown zero-atom expectation, with finite measure conversion. It is the missing nonzero BV boundary input for the original killed-scale resolvent.
-- source:
--   Genuine original Exp(R) drawdown atom proved UUID 3d98f66c; integral_indicator_one, Measure.real, Measure.map_apply, and ENNReal.ofReal_toReal in pinned Mathlib. No assumption of finite jump activity, no W(0)=0, no future-window harmonicity or stopped exit identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_bv_drawdown_zero_atom
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_actual_bv_drawdown_zero_atom_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hstanding : X.Standing) (hBV : X.BoundedVariation)
    (R φ : ℝ) (hR : 0 < R) (hφ : 0 < φ)
    (hroot : X.ψ φ = R) :
    ((P.prod (expMeasure R)).map
      (fun z : Ω × ℝ =>
        runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1))
      ({0} : Set ℝ) =
    ENNReal.ofReal (R / (φ * X.drift)) := by sorry
