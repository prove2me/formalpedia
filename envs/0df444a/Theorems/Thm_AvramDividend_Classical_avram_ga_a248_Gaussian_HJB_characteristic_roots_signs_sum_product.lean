-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a248_Gaussian_HJB_characteristic_roots_signs_sum_product
-- name    : AvramDividend.Classical.avram_ga_a248_Gaussian_HJB_characteristic_roots_signs_sum_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:38:52.566166+00:00
-- url     : https://prove2.me/theorems/7e9f6141-745c-4441-b39e-51db23ad7020
-- title:
--   Gaussian HJB scalar characteristic roots have opposite signs and exact sum/product
-- statement:
--   For the original Gaussian zerojump scalar verification ODE with nonzero Gaussian volatility and strictly positive discount rate, define characteristic roots (-c±sqrt(c²+2qσ²))/σ². The plus root is strictly positive, minus root strictly negative, their sum is -2c/σ² and product -2q/σ². The roots permit a factorised positive-origin supersolution barrier, an essential input missing from the true large Gaussian raw-cell a216 argument.
-- source:
--   Original Gaussian HJB scalar factorisation; near-origin uniform upper one-sided barrier route

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a248_Gaussian_HJB_characteristic_roots_signs_sum_product
    (sigma c q : ℝ) (hSigma : 0 < sigma) (hq : 0 < q) :
    let root : ℝ := Real.sqrt (c^2+2*q*sigma^2)
    let lambdaPlus : ℝ := (-c+root)/sigma^2
    let lambdaMinus : ℝ := (-c-root)/sigma^2
    0 < lambdaPlus ∧ lambdaMinus < 0 ∧
    lambdaPlus+lambdaMinus = -2*c/sigma^2 ∧
    lambdaPlus*lambdaMinus = -2*q/sigma^2 := by sorry
