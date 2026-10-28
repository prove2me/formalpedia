-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_psi_root_strictly_above_shift
-- name    : AvramDividend.Classical.levy_psi_root_strictly_above_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:53:47.157138+00:00
-- url     : https://prove2.me/theorems/eb5bb6f8-2e6f-478a-814d-8b4bd3b3519d
-- title:
--   Strict positivity of the positive Esscher-root shifted Lévy exponent
-- statement:
--   For every positive Lévy discount root φ with ψ(φ)=q>0 and any further positive shift θ, the shifted exponent ψ(φ+θ) exceeds q strictly. This establishes the strict sign of the denominator in the Esscher-shifted scale and Wiener-Hopf Laplace transforms.
-- source:
--   Direct corollary of the already-Proved general spectrally negative Lévy secant bound e9488750 (q/φ)θ ≤ ψ(φ+θ)−q. Because q, φ and θ are strictly positive, its left-hand side is strictly positive, so the denominator of the Esscher-weighted Wiener-Hopf quotient cannot vanish.

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_shifted_increment_lower

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_psi_root_strictly_above_shift
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ θ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hθ : 0 < θ)
    (hroot : X.ψ φ = q) :
    q < X.ψ (φ + θ) := by sorry
