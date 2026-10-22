-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_generator_add_of_jet_additive
-- name    : AvramDividend.Classical.levy_generator_add_of_jet_additive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T22:25:26.720337+00:00
-- url     : https://prove2.me/theorems/65fd7e9b-40ab-4e8c-bec1-3e2c0fefccb7
-- title:
--   Additivity of the Lévy generator and closure of its jump-integrability domain under additive derivative jets
-- statement:
--   Fix a spectrally negative Lévy triplet X and payoffs f and g for which each generator jump integrand is integrable at reserve x. Assume the usual first derivative and second iterated derivative of the sum at x equal the sums of the corresponding derivatives of f and g (as holds for sufficiently smooth functions). Prove that the generator jump integrand of f+g is integrable and that Γ(f+g)(x)=Γf(x)+Γg(x). The proof expands the compensated jump term using the first derivative assumption, closes integrability using IntegrableOn.add, applies the restricted-measure Bochner integral_add to split the jump integral, and combines the drift and Gaussian terms using the second derivative assumption and ring algebra. Unlike the exact Γ-exp formula already Proved, this result can extend generator identities from individual exponential test functions to their finite linear combinations, once smoothness and integrability are supplied. It does not assert a stochastic Dynkin/martingale theorem or the stopped HJB dividend budget.
-- source:
--   Only exact pinned generator definitions, Mathlib IntegrableOn.add/integral_add, ring arithmetic, and explicitly stated derivative jet identities. No Open imports.

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_generator_add_of_jet_additive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f g : ℝ → ℝ) (x : ℝ)
    (hf : X.GeneratorIntegrable f x)
    (hg : X.GeneratorIntegrable g x)
    (hfirst :
      deriv (fun z => f z + g z) x = deriv f x + deriv g x)
    (hsecond :
      iteratedDeriv 2 (fun z => f z + g z) x =
        iteratedDeriv 2 f x + iteratedDeriv 2 g x) :
    X.GeneratorIntegrable (fun z => f z + g z) x ∧
      X.generator (fun z => f z + g z) x =
        X.generator f x + X.generator g x := by sorry
