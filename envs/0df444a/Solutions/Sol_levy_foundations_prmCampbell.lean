-- Prove2me | solution 1 for levy_foundations_prmCampbell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:09:07.664204+00:00
-- url     : https://prove2.me/submissions/010aeeba-7eef-4381-aca8-d37aa7cd101b

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Poisson.Basic
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_poissonRandomMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_levy_foundations_measurablePRMEval
import Theorems.Thm_levy_foundations_prmEvaluationMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    {g : E → ENNReal} (hg : Measurable g) :
    ∫⁻ ω, ∫⁻ x, g x ∂(LevyFoundations.poissonRandomMeasure K X ω) ∂μ
      = ∫⁻ x, g x ∂m := by
  have hMeasSimple (s : SimpleFunc E ENNReal) :
      Measurable fun ω => s.lintegral (LevyFoundations.poissonRandomMeasure K X ω) := by
    simp only [SimpleFunc.lintegral]
    exact Finset.measurable_sum _ fun x _ =>
      measurable_const.mul
        (levy_foundations_measurablePRMEval K X
          hd.measurable_count hd.measurable_point (s.measurableSet_fiber x))
  have hEvalSimple (s : SimpleFunc E ENNReal) :
      ∫⁻ ω, s.lintegral (LevyFoundations.poissonRandomMeasure K X ω) ∂μ =
        s.lintegral m := by
    simp only [SimpleFunc.lintegral]
    rw [lintegral_finsetSum s.range
      (f := fun x ω => x * LevyFoundations.poissonRandomMeasure K X ω (s ⁻¹' {x}))
      (fun x _ => measurable_const.mul
        (levy_foundations_measurablePRMEval K X
          hd.measurable_count hd.measurable_point (s.measurableSet_fiber x)))]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [lintegral_const_mul _
      (levy_foundations_measurablePRMEval K X
        hd.measurable_count hd.measurable_point (s.measurableSet_fiber x)),
      levy_foundations_prmEvaluationMean m μ K X hd (s.measurableSet_fiber x)]
  simp_rw [lintegral_eq_iSup_eapprox_lintegral hg]
  rw [lintegral_iSup
    (fun n => hMeasSimple (SimpleFunc.eapprox g n))
    (fun i j h ω => SimpleFunc.lintegral_mono
      (SimpleFunc.monotone_eapprox g h) le_rfl)]
  exact iSup_congr fun n => hEvalSimple (SimpleFunc.eapprox g n)
