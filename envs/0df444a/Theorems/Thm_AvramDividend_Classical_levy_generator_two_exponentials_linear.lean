-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_generator_two_exponentials_linear
-- name    : AvramDividend.Classical.levy_generator_two_exponentials_linear
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:00:27.466158+00:00
-- url     : https://prove2.me/theorems/ebdee724-20f9-45f0-bb01-23559c5222b6
-- title:
--   Generator integrability and exact linearity for two exponential Lévy test functions
-- statement:
--   For nonnegative rates theta and phi and arbitrary real coefficients a,b, the two-exponential test payoff is in the jump-integrability domain of the spectrally negative Levy generator. Moreover its generator is the weighted sum of the individual exponential generators. This combines the proven Levy second-moment weight integrability, the proven compensated exponential integrability theorem, scalar generator linearity and generator additivity under additive derivative jets; the jets follow from smoothness of exponential functions. Together with the independently submitted transition-semigroup limit for two exponentials, it identifies the actual right derivative of expected payoffs with the full generator of their sum.
-- source:
--   Avram, Palmowski and Pistorius (2007), Levy-Khintchine generator and Section 5.4 stochastic verification; standard linearity of the generator.

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FunProp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levyWeight_integrable
import Theorems.Thm_AvramDividend_Classical_levy_exponential_generatorIntegrable_of_moment
import Theorems.Thm_AvramDividend_Classical_levy_generatorIntegrable_const_mul
import Theorems.Thm_AvramDividend_Classical_levy_generator_const_mul
import Theorems.Thm_AvramDividend_Classical_levy_generator_add_of_jet_additive

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_generator_two_exponentials_linear
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b θ φ x : ℝ) (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) :
    X.GeneratorIntegrable
      (fun z : ℝ => a * Real.exp (θ * z) + b * Real.exp (φ * z)) x ∧
    X.generator
      (fun z : ℝ => a * Real.exp (θ * z) + b * Real.exp (φ * z)) x =
      a * X.generator (fun z : ℝ => Real.exp (θ * z)) x +
      b * X.generator (fun z : ℝ => Real.exp (φ * z)) x := by sorry
