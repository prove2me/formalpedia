-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_boundary_left_order_of_sigma_zero
-- name    : AvramDividend.Classical.generator_boundary_left_order_of_sigma_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T12:45:41.220529+00:00
-- url     : https://prove2.me/theorems/722d571b-002f-48a5-ab8c-6726f6e634fb
-- title:
--   Pure-jump boundary generator ordering with matching first derivative, no second jet
-- statement:
--   In the zero-Gaussian spectrally negative Lévy case σ=0, a function f dominated by g on the entire left half-line (-∞,a], equal in value and first derivative at a, and with both generator jump terms integrable satisfies Γf(a)≤Γg(a). The nonlocal negative-jump integral order is obtained from the pointwise left dominance, and the Gaussian second derivative term is exactly zero, so no second-derivative assumption is imposed. This supports one-sided HJB upper-bound arguments in the bounded-variation/pure-jump branch.

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.generator_boundary_left_order_of_sigma_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 0)
    (f g : ℝ → ℝ) (a : ℝ)
    (hle : ∀ z : ℝ, z ≤ a → f z ≤ g z)
    (hat : f a = g a)
    (hder : deriv f a = deriv g a)
    (hf : X.GeneratorIntegrable f a)
    (hg : X.GeneratorIntegrable g a) :
    X.generator f a ≤ X.generator g a := by sorry
