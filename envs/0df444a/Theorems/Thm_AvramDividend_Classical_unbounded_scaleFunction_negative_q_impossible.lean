-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scaleFunction_negative_q_impossible
-- name    : AvramDividend.Classical.unbounded_scaleFunction_negative_q_impossible
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T06:58:59.257531+00:00
-- url     : https://prove2.me/theorems/d14a3b03-1013-4a7e-8171-0d20a4fa2dc0
-- title:
--   A positive monotone unbounded-variation scale function cannot have negative discount q
-- statement:
--   Direct helper for the root-connected Open leaf scaleFunction_contDiff_one_of_unbounded_variation_nonpositive_q (8b23cd38-7b0a-4469-bfb1-90feef46733d). For q<0, the canonical Laplace identity at θ=0 forces W to be integrable on the positive half-line since ψ(0)=0>q. Unbounded variation gives W(1)>0 and monotonicity gives W(x)≥W(1)>0 for x≥1. Thus W dominates a strictly positive constant over a set of infinite Lebesgue measure, contradicting integrability. The parent theorem can then reduce q≤0 to the genuine q=0 smoothness case by `lt_or_eq_of_le`. This has a non-circular proof using only Proved levy_laplace_exponent_zero, scaleFunction_strict_pos_of_unbounded_variation, and pinned Mathlib integration lemmas.
-- source:
--   Canonical Prove2Me definition of IsScaleFunction; monotone integrable functions on infinite measure sets.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scaleFunction_negative_q_impossible
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : q < 0)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) : False := by sorry
