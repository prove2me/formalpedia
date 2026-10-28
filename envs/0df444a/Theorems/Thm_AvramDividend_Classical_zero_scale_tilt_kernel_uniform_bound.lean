-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_scale_tilt_kernel_uniform_bound
-- name    : AvramDividend.Classical.zero_scale_tilt_kernel_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:39:04.204987+00:00
-- url     : https://prove2.me/theorems/9ca7ba54-2c07-48b2-ba6d-bfa83b0359e2
-- title:
--   Global sup bound for the q-weighted zero-scale Esscher kernel
-- statement:
--   The q-weighted exponential tilt of an admissible zero-discount scale function is bounded on the entire real line whenever q is nonnegative, θ is nonnegative and ψ(θ)>0. Pull the q factor through the real norm and apply the already proved global weighted norm bound for scale functions. Supplies the boundedness premise of the causal Neumann series continuity argument.
-- source:
--   Proved scaleFunction_global_weighted_norm_bddAbove plus norm scalar multiplication.

import Theorems.Thm_AvramDividend_Classical_scaleFunction_global_weighted_norm_bddAbove
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.zero_scale_tilt_kernel_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (q θ : ℝ) (hq : 0 ≤ q) (hθ : 0 ≤ θ) (hψ : 0 < X.ψ θ) :
    BddAbove (Set.range (fun x : ℝ =>
      ‖q * (Real.exp (-(θ * x)) * W₀ x)‖)) := by sorry
