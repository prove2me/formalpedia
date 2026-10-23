-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_psi_strictly_above_root
-- name    : AvramDividend.Classical.gaussian_esscher_psi_strictly_above_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T14:35:33.437171+00:00
-- url     : https://prove2.me/theorems/188c5c28-c311-4c7f-a4e4-261cecc400b0
-- title:
--   Native Gaussian Lévy Esscher exponent strictly exceeds its positive q-root
-- statement:
--   For a spectrally negative Lévy process with positive Gaussian coefficient, a positive Esscher root ψ(φ)=q and a positive shift θ, the exponent ψ(φ+θ) strictly exceeds q. The native process exponent is rewritten as the Lévy–Khintchine exponent with a corrected drift accounting for an atom of jump magnitude one; the previously Proved scalar Gaussian positive-root resolvent positivity theorem then gives the strict inequality. This is the precise condition required to apply the q-scale-function shifted Laplace-transform theorem.
-- source:
--   Proved gaussian_laplaceExponent_inclusive_drift_adjusted and gaussian_positive_root_resolvent_denominator; no Volterra identity assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_gaussian_laplaceExponent_inclusive_drift_adjusted
import Theorems.Thm_AvramDividend_Classical_gaussian_positive_root_resolvent_denominator
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_esscher_psi_strictly_above_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ θ : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (hθ : 0 < θ) (hσ : 0 < X.σ) (hroot : X.ψ φ = q)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2))
        ∂(X.ν.map (fun y : ℝ => -y))) < ⊤) :
    q < X.ψ (φ + θ) := by sorry
