-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_zero_scale_bounded_contractive_kernel
-- name    : AvramDividend.Classical.unbounded_zero_scale_bounded_contractive_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:15:38.574802+00:00
-- url     : https://prove2.me/theorems/fbac43ff-5037-439a-9bed-3b7c9d632967
-- title:
--   Choose a globally bounded positive Esscher renewal kernel with subunit mass
-- statement:
--   From unbounded variation and a zero-discount scale, choose a Laplace exponent θ where ψ(θ)>q>0. Then K(x)=q exp(-θx)W0(x) is a continuous, globally bounded, nonnegative causal kernel of finite positive-half-line mass ρ=q/ψ(θ)∈(0,1). This packages the complete kernel estimates and the strict exponent inequality needed to construct a positive-discount scale by a Neumann series.
-- source:
--   Proved eventual psi growth, zero-scale origin continuity, tilted-kernel support and positivity, global weighted norm bound and all-parameter Laplace identity.

import Theorems.Thm_AvramDividend_Classical_chat04_psi_eventually_gt_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuous_of_zero_origin
import Theorems.Thm_AvramDividend_Classical_zero_scale_tilt_kernel_uniform_bound
import Theorems.Thm_AvramDividend_Classical_zero_scale_kernel_tilt_all_parameter_laplace
import Theorems.Thm_AvramDividend_Classical_unbounded_zero_scale_tilt_kernel_causal_nonnegative
import Mathlib.Tactic.FunProp
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_zero_scale_bounded_contractive_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (q : ℝ) (hq : 0 < q) :
    ∃ θ ρ : ℝ, ∃ K : ℝ → ℝ,
      0 ≤ θ ∧ q < X.ψ θ ∧ 0 < ρ ∧ ρ < 1 ∧
      Continuous K ∧
      BddAbove (Set.range (fun x : ℝ => ‖K x‖)) ∧
      IntegrableOn K (Ioi (0 : ℝ)) volume ∧
      (∫ x in Ioi (0 : ℝ), K x ∂volume) = ρ ∧
      (∀ x : ℝ, x ≤ 0 → K x = 0) ∧
      (∀ x : ℝ, 0 ≤ K x) ∧
      (∀ x : ℝ, K x = q * (Real.exp (-(θ * x)) * W₀ x)) := by sorry
