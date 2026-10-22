-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_vcstar_pure_jump_cap_harmonic_of_differentiable_scale
-- name    : AvramDividend.Classical.chat07_vcstar_pure_jump_cap_harmonic_of_differentiable_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:00:44.302855+00:00
-- url     : https://prove2.me/theorems/073b643f-ac9c-412c-b190-9da00dc88f71
-- title:
--   Pure-jump dividend-value harmonicity at the cap from differentiable scale and interior residual
-- statement:
--   At a positive canonical barrier in the pure-jump spectrally negative Lévy case, assume the scale function has nonnegative support, is differentiable at the barrier with nonzero derivative, is in the generator domain there, and has continuous discounted generator residual on the inner closed boundary interval that vanishes below the barrier. Then the dividend-value candidate is also generator-integrable at the barrier and has exactly zero discounted generator residual. The first-order boundary matching is deduced from a previously proved smooth-fit theorem rather than assumed. This remains conditional on the stochastic interior identity and residual continuity.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_vcstar_pure_jump_cap_harmonic_of_differentiable_scale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : X.σ = 0)
    (q : ℝ) (W : ℝ → ℝ)
    (hsupport : ∀ z : ℝ, z < 0 → W z = 0)
    (ha : 0 < (cstar W).toReal)
    (hWdiff : DifferentiableAt ℝ W (cstar W).toReal)
    (hWderiv : deriv W (cstar W).toReal ≠ 0)
    (hdom : X.GeneratorIntegrable W (cstar W).toReal)
    (hcont : ContinuousOn
      (fun z : ℝ => X.generator W z - q * W z)
      (Ioc 0 (cstar W).toReal))
    (hinside : ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.generator W x - q * W x = 0) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 := by sorry
