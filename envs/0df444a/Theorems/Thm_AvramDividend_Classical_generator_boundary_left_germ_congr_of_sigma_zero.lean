-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_boundary_left_germ_congr_of_sigma_zero
-- name    : AvramDividend.Classical.generator_boundary_left_germ_congr_of_sigma_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T11:13:54.054463+00:00
-- url     : https://prove2.me/theorems/a4bcee04-aa7e-49f7-91b0-584e38f9a8b2
-- title:
--   Zero-Gaussian boundary generator congruence from only first derivative and left-side values
-- statement:
--   For a spectrally negative Lévy process with zero Gaussian coefficient σ, any two functions agreeing on all reserves at or below a and having equal ordinary first derivative at a have equivalent integrability of their nonlocal generator jump parts and identical generator values at a. No second-derivative matching or existence is needed because σ² times the second iterated derivative disappears. This is directly useful in the bounded-variation or pure-jump branch of the endpoint barrier value verification, where demanding a C² smooth fit would impose unjustified regularity.

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.generator_boundary_left_germ_congr_of_sigma_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 0)
    (f g : ℝ → ℝ) (a : ℝ)
    (hleft : ∀ z : ℝ, z ≤ a → f z = g z)
    (hder : deriv f a = deriv g a) :
    (X.GeneratorIntegrable f a ↔ X.GeneratorIntegrable g a) ∧
      X.generator f a = X.generator g a := by sorry
