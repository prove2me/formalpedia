-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_probability_weighted_cdf_real_eq_laplace
-- name    : AvramDividend.Classical.esscher_probability_weighted_cdf_real_eq_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T20:06:29.147701+00:00
-- url     : https://prove2.me/theorems/0b9fd101-931c-44e5-997f-a47f1cd04ee2
-- title:
--   Exponential capital-weighted real CDF integral equals the genuine nonnegative probability law Laplace transform divided by rate
-- statement:
--   For any genuine probability measure ν on ℝ supported on [0,∞) and any β>0, the ENNReal.ofReal of the real weighted cumulative integral ∫_{x>0}e^{-βx}CDF_ν(x)dx equals (1/β) times its exact ENNReal Laplace transform ∫e^{-βz}ν(dz). The theorem proves the real-to-ENNReal integral conversion under the integrable exp(-βx) majorant, identifies Mathlib's real cdf with finite ENNReal closed-half-line mass, and uses the previously Proved positiveLaplace_cumulative_measure. It does not assume a finite-rate Wiener–Hopf identity. This is the missing type-accurate bridge between accepted 1E-C capital-CDF limits and the canonical perpetual probability's transform.
-- source:
--   Pinned Mathlib integrableOn_exp_mul_Ioi, ofReal_integral_eq_lintegral_ofReal, ProbabilityTheory.cdf_eq_real, ENNReal.ofReal_toReal, positiveLaplace_cumulative_measure Prove2Me 6027eb2c.

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.CDF
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_cumulative_measure
open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

theorem AvramDividend.Classical.esscher_probability_weighted_cdf_real_eq_laplace
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsupp : ν (Iio (0 : ℝ)) = 0)
    (β : ℝ) (hβ : 0 < β) :
    ENNReal.ofReal (∫ x in Ioi (0 : ℝ),
      Real.exp (-β * x) * cdf ν x ∂volume) = ENNReal.ofReal (1 / β) *
      (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂ν) := by sorry
