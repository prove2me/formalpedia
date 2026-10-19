-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_boundary_left_germ_congr
-- name    : AvramDividend.Classical.generator_boundary_left_germ_congr
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T11:09:11.403712+00:00
-- url     : https://prove2.me/theorems/d9709c0b-4215-4651-9f96-6594f082fc68
-- title:
--   Left-germ and boundary-jet congruence for the nonlocal Lévy generator
-- statement:
--   Let f and g agree pointwise on (-∞,a] and have identical first derivative and second iterated derivative at a. Then the exact spectrally negative Lévy generatorIntegrand functions agree for every negative jump y at a, so generator integrability for f and g is equivalent and their full generators are equal at the boundary. The theorem includes the nonlocal negative-jump integral, not merely local differential terms. It does not assume scale-function harmonicity and is a reusable exact boundary-transfer lemma for the comparison between a scaled scale function and the dividend barrier candidate.

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.generator_boundary_left_germ_congr
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f g : ℝ → ℝ) (a : ℝ)
    (hleft : ∀ z : ℝ, z ≤ a → f z = g z)
    (hder : deriv f a = deriv g a)
    (hsecond : iteratedDeriv 2 f a = iteratedDeriv 2 g a) :
    (X.GeneratorIntegrable f a ↔ X.GeneratorIntegrable g a) ∧
      X.generator f a = X.generator g a := by sorry
