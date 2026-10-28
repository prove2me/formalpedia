-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_deterministic_horizon_scale_l2_bound
-- name    : AvramDividend.Classical.chat04_killed_deterministic_horizon_scale_l2_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:31:43.717757+00:00
-- url     : https://prove2.me/theorems/294fb6fa-969e-4649-b1db-890b0cae4261
-- title:
--   Killed deterministic-horizon q-scale rewards inherit the uniform L² bound
-- statement:
--   For any measurable history-survival event S, the squared discounted q-scale reward restricted to S remains integrable and obeys the same explicit deterministic-horizon second-moment upper bound as the unrestricted reward. This is a necessary uniform-integrability input for passing to the initial-time limit of truly killed scale expectations and proving the unbounded-variation killed semigroup harmonicity behind strict two-sided exit.
-- source:
--   Direct import of Proved chat04_deterministic_horizon_scale_l2_uniform_bound UUID 19551a5a. Generic measurableSet argument will be instantiated with Proved one-sided closed-horizon survival measurability UUID 398891d8. Downstream: killed expectation a885f0b3, stopped-scale 09663d0d.

import Theorems.Thm_AvramDividend_Classical_chat04_deterministic_horizon_scale_l2_uniform_bound
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Notation.Indicator

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat04_killed_deterministic_horizon_scale_l2_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (N t : ℝ≥0) (htN : t ≤ N)
    (S : Set Ω) (hS : MeasurableSet S) :
    Integrable (fun ω =>
      (S.indicator (fun u => Real.exp (-(q * (t : ℝ))) *
        W (x + X.X t u)) ω)^2) P ∧
    (∫ ω, (S.indicator (fun u => Real.exp (-(q * (t : ℝ))) *
        W (x + X.X t u)) ω)^2 ∂P) ≤
      ((X.ψ θ - q)⁻¹)^2 *
        Real.exp (2 * θ * (x + 1) +
          (N : ℝ) * max (X.ψ (2 * θ)) 0) := by sorry
