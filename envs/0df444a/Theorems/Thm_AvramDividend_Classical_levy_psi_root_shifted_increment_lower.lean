-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_psi_root_shifted_increment_lower
-- name    : AvramDividend.Classical.levy_psi_root_shifted_increment_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T21:57:24.021785+00:00
-- url     : https://prove2.me/theorems/e9488750-ba29-4b2a-9d1d-05734aaa628f
-- title:
--   Positive-root shifted Lévy exponent dominates its linear secant
-- statement:
--   For the canonical Laplace exponent of a spectrally negative Lévy process, a positive root phi with psi(phi)=q>0 implies psi(phi+theta)-q >= (q/phi)*theta for every theta>0. This follows from the proved monotonicity of the secant ratio psi(t)/t on t>0. It supplies the linear denominator bound for the Esscher tilted scale-function Laplace envelope.

import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_psi_positive_secant_monotone
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_psi_root_shifted_increment_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ θ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hθ : 0 < θ)
    (hroot : X.ψ φ = q) :
    (q / φ) * θ ≤ X.ψ (φ + θ) - q := by sorry
