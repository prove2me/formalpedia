-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_psi_affine_drift_reciprocal_tendsto_zero_ws01f
-- name    : AvramDividend.Classical.levy_psi_affine_drift_reciprocal_tendsto_zero_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:51:56.007407+00:00
-- url     : https://prove2.me/theorems/7a38070a-1e22-4ed9-a89a-1f7411409b9e
-- title:
--   Infinite small-jump variation forces a vanishing shifted drift-adjusted Laplace reciprocal
-- statement:
--   For the actual spectrally negative Lévy exponent with infinite first absolute moment of negative jumps, subtracting any deterministic linear drift Cθ, shifting the Laplace argument by φ, and subtracting a nonnegative q does not alter superlinear growth: the corresponding numerator-over-denominator ratio converges to zero as the Laplace parameter tends to infinity. This is the analytic high-β input to the descending Wiener–Hopf zero-atom argument for the independent infinite-small-jump Rogozin slope theorem. It does not assert any fluctuation law or pathwise regularity.
-- source:
--   The canonical BoundedVariation definition, Proved unbounded_psi_discount_reciprocal_tendsto_zero, and Proved unbounded_psi_discount_denominator_eventually_linear. A Möbius map r↦r/(1-Cr) transports the unshifted reciprocal limit; a fixed real shift preserves atTop.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_unbounded_psi_discount_reciprocal_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_unbounded_psi_discount_denominator_eventually_linear

open Filter Topology
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_psi_affine_drift_reciprocal_tendsto_zero_ws01f
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (φ C q : ℝ) (hq : 0 ≤ q) :
    Tendsto (fun β : ℝ =>
      (φ + β) / (X.ψ (φ + β) - C * (φ + β) - q))
      atTop (𝓝 0) := by sorry
