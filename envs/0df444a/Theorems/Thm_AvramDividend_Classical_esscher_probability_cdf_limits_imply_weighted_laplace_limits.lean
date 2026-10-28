-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_probability_cdf_limits_imply_weighted_laplace_limits
-- name    : AvramDividend.Classical.esscher_probability_cdf_limits_imply_weighted_laplace_limits
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:17:41.226815+00:00
-- url     : https://prove2.me/theorems/0bf634fd-5a21-4348-b978-ad0ae7b83c60
-- title:
--   Pointwise CDF convergence of genuine probability laws implies convergence of their exponentially weighted capital transforms
-- statement:
--   Let μ_n and ν be genuine probability measures on the real line and suppose that for every real threshold x, the finite-measure CDF values μ_n((−∞,x]) converge in ENNReal to ν((−∞,x]). Then for every β>0, the real capital integrals ∫_{x>0} e^{-βx}CDF_{μ_n}(x) dx converge to the analogous integral for ν. The proof converts bounded ENNReal CDF convergence to real CDF convergence using the finite-measure toReal continuity theorem, obtains automatic Borel measurability and 0≤CDF≤1 from Mathlib, and invokes the independently proved exponentially weighted CDF dominated convergence theorem. This is reusable for the true Esscher-clock measures and does not assume Wiener–Hopf.
-- source:
--   Pinned Mathlib ProbabilityTheory.cdf_eq_real, monotone_cdf, cdf_nonneg, cdf_le_one, ENNReal.tendsto_toReal_iff, measure_ne_top; proven C4 weighted CDF dominated convergence theorem.

import Mathlib.Probability.CDF
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_cdf_exp_weighted_integral_tendsto
open AvramDividend.Classical ProbabilityTheory MeasureTheory Filter Set
open scoped ENNReal

theorem AvramDividend.Classical.esscher_probability_cdf_limits_imply_weighted_laplace_limits
    (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    (hμ : ∀ n, IsProbabilityMeasure (μ n))
    [IsProbabilityMeasure ν]
    (hCDF : ∀ x : ℝ,
      Tendsto (fun n : ℕ => μ n (Iic x)) atTop (nhds (ν (Iic x))))
    (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun n : ℕ => ∫ x in Ioi (0 : ℝ),
      Real.exp (-β * x) * cdf (μ n) x ∂volume)
      atTop (nhds (∫ x in Ioi (0 : ℝ),
        Real.exp (-β * x) * cdf ν x ∂volume)) := by sorry
