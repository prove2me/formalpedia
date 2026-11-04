-- Prove2me | solution 1 for levy_foundations_withDensityConvolutionFormula
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T00:28:05.307974+00:00
-- url     : https://prove2.me/submissions/d9a7004c-2a94-44bb-8be9-19cb53ec5a1d

import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_arrivalGammaDensity
open MeasureTheory ProbabilityTheory Filter Complex
open scoped ENNReal NNReal

theorem solution
    {f g : ℝ → ℝ≥0∞} [SFinite (volume.withDensity g)]
    (hf : Measurable f) (hg : Measurable g) :
    (volume.withDensity f) ∗ (volume.withDensity g) =
      volume.withDensity (fun z => ∫⁻ x, f x * g (z - x)) := by
  ext s hs
  have key : ∀ x : ℝ, volume.withDensity g (Prod.mk x ⁻¹' ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' s))
      = ∫⁻ z in s, g (z - x) := by
    intro x
    have hA : MeasurableSet (Prod.mk x ⁻¹' ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' s)) :=
      measurable_prodMk_left (measurable_add hs)
    rw [withDensity_apply _ hA]
    have := (measurePreserving_add_left (volume : Measure ℝ) x).setLIntegral_comp_preimage hs
      (f := fun z => g (z - x)) (hg.comp (measurable_id.sub_const x))
    have e : Prod.mk x ⁻¹' ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' s) = (fun y => x + y) ⁻¹' s := rfl
    rw [e]
    simpa using this
  rw [Measure.conv, Measure.map_apply measurable_add hs, withDensity_apply _ hs,
    Measure.prod_apply (measurable_add hs),
    lintegral_withDensity_eq_lintegral_mul _ hf
      (measurable_measure_prodMk_left (measurable_add hs))]
  have h2 : ∀ x : ℝ, f x * ∫⁻ z in s, g (z - x) = ∫⁻ z in s, f x * g (z - x) :=
    fun x => (lintegral_const_mul _ (hg.comp (measurable_id.sub_const x))).symm
  simp_rw [Pi.mul_apply, key, h2]
  exact lintegral_lintegral_swap
    ((hf.comp measurable_fst).mul (hg.comp (measurable_snd.sub measurable_fst))).aemeasurable
