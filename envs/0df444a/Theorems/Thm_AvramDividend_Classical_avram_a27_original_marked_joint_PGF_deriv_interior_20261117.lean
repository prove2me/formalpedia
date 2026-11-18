-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_marked_joint_PGF_deriv_interior_20261117
-- name    : AvramDividend.Classical.avram_a27_original_marked_joint_PGF_deriv_interior_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:45:45.054859+00:00
-- url     : https://prove2.me/theorems/f966b805-d26c-4216-a8b1-0d89f76c1544
-- title:
--   Original marked jump PGF has its exact first derivative in the interior of the unit generating interval
-- statement:
--   For the unchanged finite-activity spectrally negative Levy process and original physical negative jump count K_t and marked sum J_t, the function z ↦ E[z^{K_t} exp(theta J_t)] is differentiable for 0<z<1. Its derivative equals E[K_t z^{K_t−1} exp(theta J_t)]. The derivative is dominated by the integrable original weighted count K_t exp(theta J_t) and therefore can pass under the integral. No auxiliary independent jump mark representation is assumed.
-- source:
--   Pinned Mathlib hasDerivAt_integral_of_dominated_loc_of_deriv_le, hasDerivAt_pow, Proved A27 physical marked PGF integrability cc395132 and weighted count 783d64bc.

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_exp_weighted_negative_jump_count_integrable_rate_bound_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_marked_joint_PGF_deriv_interior_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal)
    (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun x : ℝ => ∫ ω, x ^ (K ω) * Real.exp (θ * J ω) ∂P)
      (∫ ω, ((K ω : ℝ) * z ^ (K ω - 1)) * Real.exp (θ * J ω) ∂P)
      z := by sorry
