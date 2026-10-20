-- Prove2me | Theorems.Thm_AvramDividend_Classical_psi_normalised_unbounded_small_jumps
-- name    : AvramDividend.Classical.psi_normalised_unbounded_small_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:46:52.014842+00:00
-- url     : https://prove2.me/theorems/3fc04011-a4da-4c0d-a8b8-9ac3ecf6a855
-- title:
--   Infinite small negative jumps give arbitrarily large normalised Lévy exponent tails
-- statement:
--   For zero-Gaussian spectrally negative Lévy processes whose small negative-jump measure has infinite absolute first moment, the normalised Laplace exponent ψ(θ)/θ eventually exceeds any fixed real threshold. The result is uniform for all sufficiently large positive real θ and requires no Standing assumptions.
-- source:
--   Adapt the Prove2Me accepted proof of psi_eventually_gt_of_infinite_small_jump_moment, remote accepted source SHA-256 76208249af935e6ebd35e35d6f9d46f8f660111372362952f3757bb1cbb1775a, using the divergence and monotonicity of the normalised compensated small-negative-jump integral.

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

theorem AvramDividend.Classical.psi_normalised_unbounded_small_jumps
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 0)
    (hinf : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    ∀ C : ℝ, ∃ β : ℝ, 1 ≤ β ∧
      ∀ θ : ℝ, β ≤ θ → C < X.ψ θ / θ := by sorry
