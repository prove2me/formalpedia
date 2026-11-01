-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_exponential_generator_linear
-- name    : AvramDividend.Classical.avram_wave4_01_finite_exponential_generator_linear
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:00:48.054114+00:00
-- url     : https://prove2.me/theorems/dd86b696-f8ac-42de-880b-045d41aae289
-- title:
--   Full original Lévy generator integrability and exact linearity for every finite signed exponential test family
-- statement:
--   For the actual spectrally negative Lévy process, every finite signed real linear combination of exponential payoffs exp(theta_i x) with nonnegative rates belongs to the canonical compensated nonlocal generator integrability domain. The complete generator, including drift, Gaussian second derivative and compensated jump integral, equals the corresponding finite signed sum of individual exponential generators. This extends the previously Proved two-exponential generator closure and matches the canonically Proved original transition semigroup finite-family right slope, without claiming a general stopped Dynkin formula.
-- source:
--   Proved levy_generator_add_of_jet_additive 65fd7e9b, levy_generatorIntegrable_const_mul f464799e, levy_generator_const_mul 9f9674c3, levy_exponential_generatorIntegrable_of_moment 4f44df97 and levyWeight_integrable, plus pinned Mathlib C2/derivative finite induction.

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
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

theorem AvramDividend.Classical.avram_wave4_01_finite_exponential_generator_linear
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (coeff rate : ι → ℝ) (hrate : ∀ i ∈ s, 0 ≤ rate i)
    (x : ℝ) :
    X.GeneratorIntegrable
      (fun z : ℝ => ∑ i ∈ s, coeff i * Real.exp (rate i * z)) x ∧
    X.generator
      (fun z : ℝ => ∑ i ∈ s, coeff i * Real.exp (rate i * z)) x =
      ∑ i ∈ s, coeff i *
        X.generator (fun z : ℝ => Real.exp (rate i * z)) x := by sorry
