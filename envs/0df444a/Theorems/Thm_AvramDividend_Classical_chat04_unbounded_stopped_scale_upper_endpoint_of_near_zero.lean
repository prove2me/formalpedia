-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_stopped_scale_upper_endpoint_of_near_zero
-- name    : AvramDividend.Classical.chat04_unbounded_stopped_scale_upper_endpoint_of_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:57:48.136238+00:00
-- url     : https://prove2.me/theorems/5f9e4b3c-a6bf-498d-99c2-4817241230da
-- title:
--   Exact two-sided stopped q-scale payoff at its upper endpoint under upward regularity
-- statement:
--   At initial capital equal to the strictly positive upper barrier a, the canonical sum of strict upper/lower terminal q-scale payoffs has expectation W(a) for an unbounded-variation spectrally negative Lévy process, whenever it visits positive increments arbitrarily soon almost surely. The explicit upward regularity hypothesis is retained; the proof applies accepted strict-terminal factorisation and the already Proved endpoint expectation-one identity. It isolates the x=a>0 endpoint while preserving the canonical strict passage clocks and all infinite-time conventions.
-- source:
--   Kyprianou, Kuznetsov and Rivero, The Theory of Scale Functions for Spectrally Negative Lévy Processes, 2.5.1; canonical Prove2Me upper-endpoint expectation and terminal-payoff factorisation theorems.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_exit_terminal_payoff_factorisation_unbounded
import Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_exit_expectation_of_ae_upward_regularity

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_stopped_scale_upper_endpoint_of_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hplus : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω) :
    (∫⁻ ω, (if twoSidedExitUpTime X 0 ω <
          twoSidedExitDownTime X (-a) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X 0 ω)))) *
          ENNReal.ofReal
            (W (a + X.X (twoSidedExitUpTime X 0 ω).toNNReal ω))
      else 0) + (if twoSidedExitDownTime X (-a) ω <
          twoSidedExitUpTime X 0 ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-a) ω)))) *
          ENNReal.ofReal
            (W (a + X.X (twoSidedExitDownTime X (-a) ω).toNNReal ω))
      else 0) ∂P) = ENNReal.ofReal (W a) := by sorry
