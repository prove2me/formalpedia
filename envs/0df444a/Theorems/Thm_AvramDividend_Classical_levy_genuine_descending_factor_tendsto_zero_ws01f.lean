-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_genuine_descending_factor_tendsto_zero_ws01f
-- name    : AvramDividend.Classical.levy_genuine_descending_factor_tendsto_zero_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:21:45.891787+00:00
-- url     : https://prove2.me/theorems/de30158b-78a6-4d9c-bffa-8ee3c09bdae5
-- title:
--   Infinite-small-jump Lévy variation forces the full descending Wiener–Hopf real factor to vanish at high Laplace parameter
-- statement:
--   For the genuine infinite-small-jump spectrally negative Lévy exponent, the entire scalar real expression appearing in the authentic finite-clock descending Wiener–Hopf factor tends to zero as β→+∞. This analytic theorem handles the fixed shift φ and discount p, with no stochastic distributional assertion or atomlessness assumed. Its input is the already accepted affine-drift reciprocal plus the actual denominator growth bound.
-- source:
--   Canonical Lévy exponent, Proved levy_psi_affine_drift_reciprocal_tendsto_zero_ws01f and Proved unbounded_psi_discount_denominator_eventually_linear; exact real field identities off a bounded exceptional parameter set.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_psi_affine_drift_reciprocal_tendsto_zero_ws01f
import Theorems.Thm_AvramDividend_Classical_unbounded_psi_discount_denominator_eventually_linear

open Filter Topology MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_genuine_descending_factor_tendsto_zero_ws01f
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (φ q p lam : ℝ) (hqp : 0 ≤ q + p) :
    Tendsto (fun β : ℝ =>
      (p / lam) * ((lam - β) /
        (p - (X.ψ (φ + β) - q)))) atTop (𝓝 0) := by sorry
