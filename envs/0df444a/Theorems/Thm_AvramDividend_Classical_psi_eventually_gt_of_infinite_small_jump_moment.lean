-- Prove2me | Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_infinite_small_jump_moment
-- name    : AvramDividend.Classical.psi_eventually_gt_of_infinite_small_jump_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:32:45.118313+00:00
-- url     : https://prove2.me/theorems/0129b889-7aee-41c9-9475-11b37a46af7b
-- title:
--   Infinite small-jump first moment forces eventual Lévy-exponent growth
-- statement:
--   For a zero-Gaussian canonical spectrally negative Lévy process whose small negative jumps have infinite absolute first moment, the Laplace exponent eventually exceeds every positive q for all sufficiently large real Laplace parameters.
-- source:
--   Compose the Prove2Me real divergence of normalised compensated small-jump integrals, real-parameter monotonicity, finite large-negative-jump mass and the canonical normalised psi lower bound. One sufficiently large integer sample transfers to every larger real θ.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_small_negative_compensated_div_integrable
import Theorems.Thm_AvramDividend_Classical_levy_large_negative_jump_unit_integrable
import Theorems.Thm_AvramDividend_Classical_negative_compensated_real_integral_tendsto_atTop
import Theorems.Thm_AvramDividend_Classical_negative_compensated_integral_mono
import Theorems.Thm_AvramDividend_Classical_psi_normalised_lower_bound_small

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.psi_eventually_gt_of_infinite_small_jump_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 0)
    (hinf : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (q : ℝ) (hq : 0 < q) :
    ∃ β₀ : ℝ, 0 ≤ β₀ ∧ ∀ θ : ℝ, β₀ ≤ θ → q < X.ψ θ := by sorry
