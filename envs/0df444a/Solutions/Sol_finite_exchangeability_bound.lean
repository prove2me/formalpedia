-- Prove2me | solution 1 for finite_exchangeability_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:38:15.160856+00:00
-- url     : https://prove2.me/submissions/e861f773-f325-4203-8767-334f771851be

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Mathlib.Probability.Moments.SubGaussian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization

set_option autoImplicit true
@[expose] public section
public section
universe u v
open MeasureTheory ENNReal
theorem _root_.solution
    {Ω G : Type*} [MeasurableSpace Ω] [Fintype G] [Nonempty G]
    {ν : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure ν]
    (T : G → Ω → Ω)
    (S : Set Ω)
    (hT : ∀ g, MeasureTheory.MeasurePreserving (T g) ν ν)
    (hS0 : MeasureTheory.NullMeasurableSet S ν)
    (B : ENNReal)
    (hpointwise :
      ∀ z, (∑ g : G,
        (((T g) ⁻¹' S).indicator (1 : Ω → ENNReal)) z)
          ≤ B * (Fintype.card G : ENNReal)) :
    ν S ≤ B := by
  classical
  let I : G → Ω → ENNReal := fun g => ((T g) ⁻¹' S).indicator 1
  have hI_ae : ∀ g ∈ (Finset.univ : Finset G), AEMeasurable (I g) ν := fun g _ =>
    aemeasurable_one.indicator₀ (hS0.preimage (hT g).quasiMeasurePreserving)
  have hmain :
      (Fintype.card G : ENNReal) * ν S ≤ B * (Fintype.card G : ENNReal) := by
    calc (Fintype.card G : ENNReal) * ν S
        = ∑ _g : G, ν S := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ g : G, ν ((T g) ⁻¹' S) := by
            exact Finset.sum_congr rfl fun g _ => ((hT g).measure_preimage hS0).symm
      _ = ∑ g : G, ∫⁻ z, I g z ∂ν := by
            exact Finset.sum_congr rfl fun g _ =>
              (MeasureTheory.lintegral_indicator_one₀
                (hS0.preimage (hT g).quasiMeasurePreserving)).symm
      _ = ∫⁻ z, ∑ g : G, I g z ∂ν := by
            exact (MeasureTheory.lintegral_finsetSum' Finset.univ hI_ae).symm
      _ ≤ ∫⁻ _z, B * (Fintype.card G : ENNReal) ∂ν := by
            exact MeasureTheory.lintegral_mono_ae (Filter.Eventually.of_forall hpointwise)
      _ = B * (Fintype.card G : ENNReal) := by
            simp [MeasureTheory.lintegral_const, MeasureTheory.IsProbabilityMeasure.measure_univ]
  have hcard_ne_zero : (Fintype.card G : ENNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcard_ne_top : (Fintype.card G : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  exact (ENNReal.mul_le_mul_iff_left hcard_ne_zero hcard_ne_top).mp (by rwa [mul_comm] at hmain)
