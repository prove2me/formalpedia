-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_purejump_UBV_zero_ladder_renewal_measure_exists
-- name    : AvramDividend.Classical.avram_f6_purejump_UBV_zero_ladder_renewal_measure_exists
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:45:16.685126+00:00
-- url     : https://prove2.me/theorems/2fa29eaf-a835-47c5-ad9a-99fe6573547b
-- title:
--   Original pure-jump UBV ladder renewal measure realises the scale derivative Laplace transform
-- statement:
--   For every standing spectrally negative pure-jump Lévy process of unbounded variation, construct its physical zero-discount scale renewal measure ν on (0,∞), with no atoms and locally finite cumulative measure and transform ∫exp(-θ y)ν(dy)=θ/ψ(θ) for every θ≥0 with ψ(θ)>0. This is the actual stochastic fluctuation/ladder-height renewal source. It is the single substantive missing source for the purejump zero-discount q-scale existence theorem; existing proved renewal-CDF continuity and monotonicity, and the newly submitted generalised Tonelli lemma, assemble ν into a scale function. An Esscher tilt at the positive root may be needed if X drifts to negative infinity; source exactness requires retaining the original ψ.
-- source:
--   Avram–Palmowski–Pistorius (2007), spectrally negative scale-function foundations; Kyprianou fluctuation theory renewal potential of the ladder-height process. Same analytical shape as Open Gaussian renewal measure e19eb951-1976-4fde-a73c-49390524d288, specialised to σ=0, UBV.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_purejump_UBV_zero_ladder_renewal_measure_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0) :
    ∃ ν : Measure ℝ,
      (ν (Iic (0 : ℝ)) = 0) ∧
      (∀ x : ℝ, ν {x} = 0) ∧
      (∀ x : ℝ, 0 ≤ x → ν (Ioc (0 : ℝ) x) < ⊤) ∧
      (∀ θ : ℝ, 0 ≤ θ → 0 < X.ψ θ →
        IntegrableOn (fun y : ℝ => Real.exp (-(θ * y))) (Ioi 0) ν ∧
        ∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) ∂ν = θ / X.ψ θ) := by sorry
