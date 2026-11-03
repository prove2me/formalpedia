-- Prove2me | solution 1 for levy_foundations_poissonCountCellIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:48:35.376624+00:00
-- url     : https://prove2.me/submissions/f5a191c0-b26b-42e0-be0d-b226639bc8a4

import Mathlib.Probability.Independence.Integration
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Theorems.Thm_levy_foundations_independentPieceCountMarks

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (k j : ℕ) (ψ : (ℕ → E) → ℂ)
    (hψ : Measurable ψ) :
    ∫ ω in {ω | K k ω = j}, ψ (fun n => X k n ω) ∂μ =
      (μ.real {ω | K k ω = j} : ℂ) *
        ∫ ω, ψ (fun n => X k n ω) ∂μ := by
  have hmeas : MeasurableSet {ω | K k ω = j} :=
    hd.measurable_count k (measurableSet_singleton j)
  have hXk_meas : Measurable (fun ω (n : ℕ) => X k n ω) :=
    measurable_pi_lambda _ fun n => hd.measurable_point k n
  have hcongr : ({ω | K k ω = j}).indicator
      (fun ω => ψ (fun n => X k n ω)) =
      fun ω => (if K k ω = j then (1 : ℂ) else 0) *
        ψ (fun n => X k n ω) := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases h : K k ω = j <;> simp [h]
  rw [← integral_indicator hmeas, hcongr]
  have hIndep : IndepFun (K k) (fun ω (n : ℕ) => X k n ω) μ :=
    levy_foundations_independentPieceCountMarks m μ K X hd k
  rw [show (∫ ω, (if K k ω = j then (1 : ℂ) else 0) *
        ψ (fun n => X k n ω) ∂μ) =
      (∫ ω, (if K k ω = j then (1 : ℂ) else 0) ∂μ) *
        ∫ ω, ψ (fun n => X k n ω) ∂μ from
      hIndep.integral_fun_comp_mul_comp
        (f := fun c : ℕ => if c = j then (1 : ℂ) else 0)
        (g := ψ) (hd.measurable_count k).aemeasurable
        hXk_meas.aemeasurable
        (measurable_of_countable _).aestronglyMeasurable
        hψ.aestronglyMeasurable]
  have hfirst : ∫ ω, (if K k ω = j then (1 : ℂ) else 0) ∂μ =
      (μ.real {ω | K k ω = j} : ℂ) := by
    have hrw : (fun ω => if K k ω = j then (1 : ℂ) else 0) =
        ({ω | K k ω = j}).indicator (fun _ => 1) := by
      funext ω
      by_cases h : K k ω = j <;> simp [Set.mem_setOf_eq, h]
    rw [hrw, integral_indicator_const (1 : ℂ) hmeas]
    simp only [Complex.real_smul, mul_one]
  rw [hfirst]
