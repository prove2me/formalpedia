-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_psi_excludes_nonpositive_one_increment_ae
-- name    : AvramDividend.Classical.positive_psi_excludes_nonpositive_one_increment_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:25:53.972368+00:00
-- url     : https://prove2.me/theorems/41b98039-640f-41c0-9a30-3f790be483bf
-- title:
--   Positive Lévy exponent excludes almost-surely nonpositive unit increment
-- statement:
--   If a spectrally negative Levy process has ψ(θ)>0 at some nonnegative θ, its one-time increment cannot be nonpositive almost surely. Otherwise exp(θ X_1)≤1 almost surely and hence its expected value is at most 1, contradicting the Lévy Laplace identity E[exp(θ X_1)]=exp(ψ(θ))>1. This is a short probability consequence required for disproving the un-killed scale-function martingale at zero under unbounded variation.
-- source:
--   SpectrallyNegativeLevy.laplace, isProbability, and exact Mathlib integral_mono_ae and Real.one_lt_exp_iff.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_psi_excludes_nonpositive_one_increment_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (hψ : 0 < X.ψ θ)
    (hNonpos : ∀ᵐ ω ∂P, X.X 1 ω ≤ 0) : False := by sorry
