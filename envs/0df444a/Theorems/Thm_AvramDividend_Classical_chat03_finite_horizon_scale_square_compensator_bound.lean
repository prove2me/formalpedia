-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_finite_horizon_scale_square_compensator_bound
-- name    : AvramDividend.Classical.chat03_finite_horizon_scale_square_compensator_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T17:13:27.078207+00:00
-- url     : https://prove2.me/theorems/34da5040-d838-4e93-83a2-b2b00ac2ae7b
-- title:
--   Fixed-horizon stopped q-scale square dominated by a compensated exponential
-- statement:
--   Assume the published q-scale function W, q≥0, θ≥0 with ψ(θ)>q, any initial capital x and increment z, and a nonnegative time 0≤t≤N. Then the squared discounted scale payoff [exp(-qt)W(x+z)]² is bounded by B² exp(2θ(x+1)+N max(ψ(2θ),0)) multiplied by exp(2θ z -t ψ(2θ)), where B=1/(ψ(θ)-q). The final factor is exactly the positive Laplace-compensated exponential martingale at 2θ, which admits bounded grid optional sampling without usual-filtration assumptions. This deterministic source-faithful inequality is the central missing algebraic input to a mesh-uniform L² estimate, valid even for negative overshoots.
-- source:
--   Chat 03 exact derivation using the already Proved discounted squared envelope AvramDividend.Classical.chat03_discounted_scale_square_exponential_bound (verify status before proving) and the Laplace-compensated exponential martingale from the published Lévy definition. Avram Palmowski Pistorius (2007) arXiv:math/0702893 Section 3.2.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_discounted_scale_square_exponential_bound
import Mathlib.Tactic.Linarith

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_finite_horizon_scale_square_compensator_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x z : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (N t : ℝ≥0) (ht : t ≤ N) :
    (Real.exp (-(q * (t : ℝ))) * W (x + z)) ^ 2 ≤
      ((X.ψ θ - q)⁻¹)^2 *
        Real.exp (2 * θ * (x + 1) + (N : ℝ) * max (X.ψ (2 * θ)) 0) *
        Real.exp (2 * θ * z - (t : ℝ) * X.ψ (2 * θ)) := by sorry
