-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_generator_const_mul
-- name    : AvramDividend.Classical.levy_generator_const_mul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T13:19:47.680934+00:00
-- url     : https://prove2.me/theorems/9f9674c3-87fb-40ab-b6e8-e8df68cfb9cf
-- title:
--   Exact scalar linearity of the compensated nonlocal Lévy generator
-- statement:
--   For the precise spectrally negative Lévy generator in the pinned Formalpedia environment, multiplication of an arbitrary real-valued function by a fixed real constant k commutes with the full generator, including its Gaussian second iterated derivative, drift derivative and compensated negative-jump integral. The pinned Mathlib field-scaling derivative identities require no differentiability assumption, and the Bochner integral scalar identity is valid for the totalised integral. The theorem is an actual operator identity, not a conditional q-harmonicity claim. It is a crucial algebraic bridge from the q-harmonicity of the scale function W to its scaled dividend-value continuation.

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_generator_const_mul
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (k x : ℝ) :
    X.generator (fun z : ℝ => k * f z) x =
      k * X.generator f x := by sorry
