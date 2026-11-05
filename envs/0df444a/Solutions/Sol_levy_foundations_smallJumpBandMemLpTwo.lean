-- Prove2me | solution 1 for levy_foundations_smallJumpBandMemLpTwo
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:10:04.881301+00:00
-- url     : https://prove2.me/submissions/7d09b352-19ec-4381-8599-583905f3c10d

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_levy_foundations_isLevyMeasure

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem solution
    (ν : Measure ℝ) [SigmaFinite ν]
    (hν : LevyFoundations.isLevyMeasure ν) (s t : ℝ) :
    MemLp ((Set.Ioc s t ×ˢ Set.Ioo (-1) 1).indicator
      (fun p : ℝ × ℝ => p.2)) 2 (volume.prod ν) := by
  have hI : Integrable (fun x : ℝ => min 1 (x ^ 2)) ν := by
    refine ⟨(continuous_const.min (continuous_pow 2)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => le_min zero_le_one (sq_nonneg x))]
    exact hν.2
  have hJ : Integrable (Set.indicator (Set.Ioc s t) (fun _ : ℝ => (1 : ℝ))) (volume : Measure ℝ) := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact integrableOn_const (by simp)
  have hmeasS : MeasurableSet (Set.Ioc s t ×ˢ Set.Ioo (-1 : ℝ) 1) :=
    measurableSet_Ioc.prod measurableSet_Ioo
  have hmeas : AEStronglyMeasurable ((Set.Ioc s t ×ˢ Set.Ioo (-1) 1).indicator
      (fun p : ℝ × ℝ => p.2)) (volume.prod ν) :=
    (measurable_snd.indicator hmeasS).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  have hprod := hJ.mul_prod hI
  refine hprod.mono' ((hmeas.pow 2)) (Filter.Eventually.of_forall fun p => ?_)
  obtain ⟨u, x⟩ := p
  simp only [Set.indicator_apply, Set.mem_prod, Set.mem_Ioc, Set.mem_Ioo, norm_pow,
    Real.norm_eq_abs, abs_pow, sq_abs, ite_mul, one_mul, zero_mul]
  split_ifs with h h' h'
  · exact le_min (by nlinarith [h.2.1, h.2.2]) le_rfl
  · exact absurd h.1 h'
  · exact le_trans (by simp) (le_min zero_le_one (sq_nonneg x))
  · simp
