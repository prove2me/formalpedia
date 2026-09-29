-- Prove2me | solution 1 for variance_eq_half_resample_difference_pi
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-24T02:30:45.982636+00:00
-- url     : https://prove2.me/submissions/2f3f83e8-34bc-4221-aa2f-003bc2a3acc9

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.IdentDistrib

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal NNReal BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    {Z : (∀ j, α j) → ℝ} (hZ : MemLp Z 2 (Measure.pi μ)) :
    variance Z (Measure.pi μ)
      = (∫ p, (Z p.1 - Z p.2) ^ 2 ∂((Measure.pi μ).prod (Measure.pi μ))) / 2 := by
  set ν := (Measure.pi μ).prod (Measure.pi μ) with hν
  have hZae : AEMeasurable Z (Measure.pi μ) := hZ.aestronglyMeasurable.aemeasurable
  have mpfst : MeasurePreserving (Prod.fst : (∀ j, α j) × (∀ j, α j) → (∀ j, α j))
      ν (Measure.pi μ) := MeasureTheory.measurePreserving_fst
  have mpsnd : MeasurePreserving (Prod.snd : (∀ j, α j) × (∀ j, α j) → (∀ j, α j))
      ν (Measure.pi μ) := MeasureTheory.measurePreserving_snd
  set W : (∀ j, α j) × (∀ j, α j) → ℝ := fun p => Z p.1 with hW
  set W' : (∀ j, α j) × (∀ j, α j) → ℝ := fun p => Z p.2 with hW'
  have hWmem : MemLp W 2 ν := hZ.comp_fst _
  have hW'mem : MemLp W' 2 ν := hZ.comp_snd _
  have hvarW : variance W ν = variance Z (Measure.pi μ) :=
    mpfst.variance_fun_comp hZae
  have hindep : IndepFun W W' ν := by
    rw [hν, hW, hW']; exact indepFun_prod₀ hZae hZae
  have e1 : Measure.map W ν = Measure.map Z (Measure.pi μ) := by
    rw [hW, show (fun p : (∀ j, α j) × (∀ j, α j) => Z p.1) = Z ∘ Prod.fst from rfl,
      ← AEMeasurable.map_map_of_aemeasurable (mpfst.map_eq ▸ hZae) measurable_fst.aemeasurable,
      mpfst.map_eq]
  have e2 : Measure.map W' ν = Measure.map Z (Measure.pi μ) := by
    rw [hW', show (fun p : (∀ j, α j) × (∀ j, α j) => Z p.2) = Z ∘ Prod.snd from rfl,
      ← AEMeasurable.map_map_of_aemeasurable (mpsnd.map_eq ▸ hZae) measurable_snd.aemeasurable,
      mpsnd.map_eq]
  have hident : IdentDistrib W W' ν ν :=
    ⟨hWmem.aestronglyMeasurable.aemeasurable, hW'mem.aestronglyMeasurable.aemeasurable,
      by rw [e1, e2]⟩
  -- Inlined resampling identity: Var(W) = ½ ∫(W−W')²  (van Handel §2.1; BLM Ch.3).
  have key : variance W ν = (∫ p, (W p - W' p) ^ 2 ∂ν) / 2 := by
    have hWm : AEStronglyMeasurable W ν := hWmem.aestronglyMeasurable
    have hW'm : AEStronglyMeasurable W' ν := hW'mem.aestronglyMeasurable
    have hWint : Integrable W ν := hWmem.integrable one_le_two
    have hW'int : Integrable W' ν := hW'mem.integrable one_le_two
    have hWsq : Integrable (fun p => W p ^ 2) ν := by
      simpa [pow_two] using hWmem.integrable_sq
    have hW'sq : Integrable (fun p => W' p ^ 2) ν := by
      simpa [pow_two] using hW'mem.integrable_sq
    have hWW' : Integrable (fun p => W p * W' p) ν :=
      hindep.integrable_mul hWint hW'int
    have hexpand : ∀ p, (W p - W' p) ^ 2
        = W p ^ 2 - 2 * (W p * W' p) + W' p ^ 2 := by intro p; ring
    have hsplit : ∫ p, (W p - W' p) ^ 2 ∂ν
        = (∫ p, W p ^ 2 ∂ν) - 2 * (∫ p, W p * W' p ∂ν) + (∫ p, W' p ^ 2 ∂ν) := by
      calc ∫ p, (W p - W' p) ^ 2 ∂ν
          = ∫ p, (W p ^ 2 - 2 * (W p * W' p) + W' p ^ 2) ∂ν := by simp_rw [hexpand]
        _ = (∫ p, (W p ^ 2 - 2 * (W p * W' p)) ∂ν) + ∫ p, W' p ^ 2 ∂ν :=
            integral_add (hWsq.sub (hWW'.const_mul 2)) hW'sq
        _ = ((∫ p, W p ^ 2 ∂ν) - ∫ p, 2 * (W p * W' p) ∂ν) + ∫ p, W' p ^ 2 ∂ν := by
            rw [integral_sub hWsq (hWW'.const_mul 2)]
        _ = (∫ p, W p ^ 2 ∂ν) - 2 * (∫ p, W p * W' p ∂ν) + (∫ p, W' p ^ 2 ∂ν) := by
            rw [integral_const_mul]
    have hmul : ∫ p, W p * W' p ∂ν = (∫ p, W p ∂ν) * (∫ p, W' p ∂ν) :=
      hindep.integral_fun_mul_eq_mul_integral hWm hW'm
    have hEeq : ∫ p, W' p ∂ν = ∫ p, W p ∂ν := hident.symm.integral_eq
    have hEsq : ∫ p, W' p ^ 2 ∂ν = ∫ p, W p ^ 2 ∂ν := by
      have := (hident.symm.comp (measurable_id.pow_const 2)).integral_eq
      simpa using this
    rw [variance_eq_sub hWmem]
    rw [hsplit, hmul, hEeq, hEsq]
    have hsq : ν[W ^ 2] = ∫ p, W p ^ 2 ∂ν := by simp [Pi.pow_apply]
    have hEW : ν[W] = ∫ p, W p ∂ν := rfl
    rw [hsq, hEW]
    ring
  rw [hvarW] at key
  rw [← key]
