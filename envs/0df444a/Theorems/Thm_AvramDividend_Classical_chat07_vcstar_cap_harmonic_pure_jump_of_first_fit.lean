-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_vcstar_cap_harmonic_pure_jump_of_first_fit
-- name    : AvramDividend.Classical.chat07_vcstar_cap_harmonic_pure_jump_of_first_fit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:51:59.950395+00:00
-- url     : https://prove2.me/theorems/553c3979-2cc8-40d3-8389-ffe895dda7f9
-- title:
--   Pure-jump dividend-value cap harmonicity from first-order smooth fit
-- statement:
--   For a spectrally negative Lévy process with zero Gaussian coefficient, at a positive canonical barrier suppose the scale function is supported on nonnegative reserves, its generator is integrable at the barrier, and its generator residual is continuous through the barrier and vanishes below. If the first derivatives of the dividend value and the normalised scale branch agree at the barrier, then the full nonlocal Lévy generator of the dividend value exists there and its q-discounted residual vanishes. This result requires only first-order smooth fit in the pure-jump case and follows from accepted endpoint harmonicity and zero-Gaussian left-germ generator congruence.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_vcstar_cap_harmonic_pure_jump_of_first_fit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : X.σ = 0)
    (q : ℝ) (W : ℝ → ℝ)
    (hsupport : ∀ z : ℝ, z < 0 → W z = 0)
    (a : ℝ) (ha : 0 < a) (hbarrier : a = (cstar W).toReal)
    (hdom : X.GeneratorIntegrable W a)
    (hcont : ContinuousOn
      (fun z : ℝ => X.generator W z - q * W z) (Ioc 0 a))
    (hinside : ∀ x ∈ Ioo 0 a,
      X.generator W x - q * W x = 0)
    (hder : deriv (vcstar W) a =
      deriv (fun z : ℝ => divE (W z) (scaleDeriv W a)) a) :
    X.GeneratorIntegrable (vcstar W) a ∧
      X.generator (vcstar W) a - q * vcstar W a = 0 := by sorry
