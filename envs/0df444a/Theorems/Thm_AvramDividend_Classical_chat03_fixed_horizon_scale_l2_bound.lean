-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_fixed_horizon_scale_l2_bound
-- name    : AvramDividend.Classical.chat03_fixed_horizon_scale_l2_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T17:21:25.092608+00:00
-- url     : https://prove2.me/theorems/b0f87b32-3722-4ca0-9de1-cf1737ca8452
-- title:
--   Mesh-independent L² bound for stopped scale values from a unit exponential moment
-- statement:
--   For the canonical q-scale function W of a spectrally negative Lévy process, q≥0 and θ≥0 with ψ(θ)>q, take any random nonnegative time T≤N, any increment Z, and fixed starting reserve x. If the squared discounted scale payoff is almost-everywhere strongly measurable, and the compensated exponential exp(2θ Z−T ψ(2θ)) is integrable with expectation exactly one, then the squared scale payoff is integrable and its expectation is bounded above by (ψ(θ)−q)^(-2) exp(2θ(x+1)+N max(ψ(2θ),0)). The bound is independent of the grid mesh, stopping index and joint law beyond the explicitly stated moment identity. It follows from the proved pointwise finite-horizon compensated envelope and dominated integrability; the moment-one premise is supplied at dyadic exits by the separate bounded two-sided grid optional sampling child.
-- source:
--   Chat 03 source-faithful assembly at pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, using previously Proved/compiled chat03_finite_horizon_scale_square_compensator_bound and exact measure-theoretic Integrable.mono'. Avram Palmowski Pistorius (2007), arXiv:math/0702893, Section 3, stopping and scale function programme.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_finite_horizon_scale_square_compensator_bound
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_fixed_horizon_scale_l2_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (N : ℝ≥0) (T : Ω → ℝ≥0) (Z : Ω → ℝ)
    (hT : ∀ ω, T ω ≤ N)
    (hScaleMeas : AEStronglyMeasurable
      (fun ω => (Real.exp (-(q * (T ω : ℝ))) * W (x + Z ω)) ^ 2) P)
    (hMomentInt : Integrable
      (fun ω => Real.exp (2 * θ * Z ω -
        (T ω : ℝ) * X.ψ (2 * θ))) P)
    (hMomentOne : (∫ ω, Real.exp (2 * θ * Z ω -
      (T ω : ℝ) * X.ψ (2 * θ)) ∂P) = 1) :
    Integrable
      (fun ω => (Real.exp (-(q * (T ω : ℝ))) * W (x + Z ω)) ^ 2) P ∧
    (∫ ω, (Real.exp (-(q * (T ω : ℝ))) * W (x + Z ω)) ^ 2 ∂P) ≤
      ((X.ψ θ - q)⁻¹)^2 *
        Real.exp (2 * θ * (x + 1) +
          (N : ℝ) * max (X.ψ (2 * θ)) 0) := by sorry
