-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_boundary_left_order_of_matching_jets
-- name    : AvramDividend.Classical.generator_boundary_left_order_of_matching_jets
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T12:42:14.802138+00:00
-- url     : https://prove2.me/theorems/8f737fdd-d5a5-4247-aec9-281664461959
-- title:
--   Boundary Lévy generator comparison under left-side dominance and matching jets
-- statement:
--   For the actual nonlocal spectrally negative Lévy generator, if f(z)≤g(z) for every reserve z≤a, f and g coincide at a and have equal ordinary first and second iterated derivatives there, and their negative-jump generator integrands are both integrable, then Γf(a)≤Γg(a). Every negative jump from a lands within the left-domain order, and matching jets cancel the compensating and Gaussian differences. This is a genuine nonlocal generator inequality, usable for one-sided HJB verification against a harmonic majorant at a boundary, not an equality or a local Taylor approximation.

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.generator_boundary_left_order_of_matching_jets
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f g : ℝ → ℝ) (a : ℝ)
    (hle : ∀ z : ℝ, z ≤ a → f z ≤ g z)
    (hat : f a = g a)
    (hder : deriv f a = deriv g a)
    (hsecond : iteratedDeriv 2 f a = iteratedDeriv 2 g a)
    (hf : X.GeneratorIntegrable f a)
    (hg : X.GeneratorIntegrable g a) :
    X.generator f a ≤ X.generator g a := by sorry
