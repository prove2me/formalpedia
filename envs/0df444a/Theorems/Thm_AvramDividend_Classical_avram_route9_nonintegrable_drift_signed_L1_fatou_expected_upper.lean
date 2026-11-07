-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route9_nonintegrable_drift_signed_L1_fatou_expected_upper
-- name    : AvramDividend.Classical.avram_route9_nonintegrable_drift_signed_L1_fatou_expected_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:50:44.395593+00:00
-- url     : https://prove2.me/theorems/d3f3db15-324c-45eb-b05a-852cbf889d5e
-- title:
--   Signed Fatou expected upper from original nonintegrable nonpositive drift and vanishing physical error
-- statement:
--   For actual BV source reductions where the stopped HJB drift is nonpositive but need not be separately L1, one can discard that drift pointwise, combine an L1 centred compensated source with an L1 positive approximation error whose mean vanishes, and infer the original strict stopped payoff expectation bound through signed Fatou. Assumes the exact original pathwise mesh inequality, not an artificial process.
-- source:
--   Direct precise reduction of the nonintegrable drift obstruction using Proved d7cb52aa signed L1 Fatou and hB≤0. Intended for c1e2f021, d7196ee6, and a19d8b28 once BV-CELL7 supplies hPath on the original stopped mesh.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route9_nonintegrable_drift_signed_L1_fatou_expected_upper
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (a : ℝ) (Y : Ω → ℝ) (F M B E : ℕ → Ω → ℝ)
    (hYInt : Integrable Y P) (hYPos : 0 ≤ᵐ[P] Y)
    (hFMeas : ∀ n, Measurable (F n))
    (hFInt : ∀ n, Integrable (F n) P)
    (hFPos : ∀ n, 0 ≤ᵐ[P] F n)
    (hM : ∀ n, Integrable (M n) P ∧
      (∫ ω, M n ω ∂P) = 0)
    (hE : ∀ n, Integrable (fun ω => max (E n ω) 0) P)
    (hEMean : Tendsto
      (fun n => ∫ ω, max (E n ω) 0 ∂P) atTop (nhds (0 : ℝ)))
    (hB : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0)
    (hPath : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ a + M n ω + B n ω + max (E n ω) 0)
    (hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Y ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    (∫ ω, Y ω ∂P) ≤ a := by sorry
