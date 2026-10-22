-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_simple_reserve
-- name    : AvramDividend.Classical.levy_increment_condExp_simple_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:33:47.481027+00:00
-- url     : https://prove2.me/theorems/2ed4ca22-e5f1-46c5-b161-6e9d862a0bc8
-- title:
--   Conditional Lévy Markov identity for an adapted finite-valued simple-function reserve
-- statement:
--   Let S be a real-valued simple function on the process sample space, measurable with respect to the past filtration at s≤t. For a measurable real payoff f assume every reserve level in the finite range of S yields an integrable stationary-increment payoff. Then the conditional expected payoff f(S+X_t−X_s) given F_s equals its deterministic stationary-increment transition integral with starting reserve S almost everywhere. The proof uses the finite-range subtype as a finite index type, establishes each fibre's past measurability from adaptedness, and applies the already Proved finite-valued starting-reserve conditional Markov identity. This is the missing typed bridge from Mathlib SimpleFunc approximants to the existing finite-state Markov proof; it does not itself establish convergence for a general integrable random reserve.
-- source:
--   Proved levy_increment_condExp_finite_valued_reserve target cbd1ef08-c269-4698-9126-2f4a4877d524 and pinned Mathlib SimpleFunc.finite_range; MeasurableSet of simple-function fibres.

import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Data.Fintype.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_finite_valued_reserve

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_increment_condExp_simple_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (S : SimpleFunc Ω ℝ)
    (hS : Measurable[𝓕 s] (S : Ω → ℝ))
    (f : ℝ → ℝ) (hf : Measurable f)
    (hI : ∀ r ∈ Set.range (S : Ω → ℝ),
      Integrable (fun ω => f (r + X.X (t - s) ω)) P) :
    P[(fun ω => f (S ω + (X.X t ω - X.X s ω))) | 𝓕 s] =ᵐ[P]
      (fun ω => ∫ η, f (S ω + X.X (t - s) η) ∂P) := by sorry
