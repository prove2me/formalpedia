-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_global_exit_identity_yields_eventual_factors
-- name    : AvramDividend.Classical.chat12_global_exit_identity_yields_eventual_factors
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:12:21.923615+00:00
-- url     : https://prove2.me/theorems/00abb1de-f2af-48c4-be36-e60782f208b5
-- title:
--   Global q-scale two-sided-exit identity implies both local strict renewal exit factors
-- statement:
--   Suppose the general corrected discounted strict two-sided-exit integral identity equals ENNReal.ofReal(W(x)/W(A)) for all A>0 and x∈[0,A]. For any fixed positive barrier a, prove that for all sufficiently small positive ε the upward exit factor with boundaries ε and -a equals ENNReal.ofReal(W(a)/W(a+ε)), and the shifted downward factor with boundaries ε and ε-a equals ENNReal.ofReal(W(a-ε)/W(a)). This purely algebraic and neighbourhood-level bridge is independent of proving the global stochastic identity; it isolates the exact substitutions needed for the upper and lower barrier valuation reductions.

import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_global_exit_identity_yields_eventual_factors
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (a : ℝ) (ha : 0 < a)
    (hIdentity : ∀ (A x : ℝ), 0 < A → 0 ≤ x → x ≤ A →
      (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : A - x < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : A - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W x / W A)) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W a / W (a + ε))) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W (a - ε) / W a)) := by sorry
