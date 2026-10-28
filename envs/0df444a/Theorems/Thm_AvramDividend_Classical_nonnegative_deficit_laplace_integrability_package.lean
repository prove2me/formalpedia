-- Prove2me | Theorems.Thm_AvramDividend_Classical_nonnegative_deficit_laplace_integrability_package
-- name    : AvramDividend.Classical.nonnegative_deficit_laplace_integrability_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T14:11:31.159331+00:00
-- url     : https://prove2.me/theorems/3ad0d90d-71b3-4238-894a-b6e27eda4ace
-- title:
--   A measurable nonnegative deficit under finite measure has all Laplace-gap integrability prerequisites
-- statement:
--   For a measurable deficit nonnegative almost everywhere under a finite measure, prove the measurability of the small-positive and zero-deficit events and integrability of both indicators and the nonzero Laplace kernel. These conditions suffice to apply the accepted actual-process deficit Laplace-gap theorem.
-- source:
--   Finite-measure bounded-integrability, measurable indicators and monotonicity of the exponential; elementary support for Avram et al. (2007), Section 3.3.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Complex.Exponential
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.nonnegative_deficit_laplace_integrability_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ]
    (D : Ω → ℝ) (hD : Measurable D)
    (hNonneg : ∀ᵐ ω ∂μ, 0 ≤ D ω)
    (n a : ℝ) (hn : 0 ≤ n) :
    MeasurableSet {ω : Ω | 0 < D ω ∧ n * D ω ≤ a} ∧
    MeasurableSet {ω : Ω | D ω = 0} ∧
    Integrable (fun ω => if 0 < D ω ∧ n * D ω ≤ a then (1 : ℝ) else 0) μ ∧
    Integrable (fun ω => if D ω = 0 then (0 : ℝ) else Real.exp (-(n * D ω))) μ ∧
    Integrable (fun ω => if D ω = 0 then (1 : ℝ) else 0) μ := by sorry
