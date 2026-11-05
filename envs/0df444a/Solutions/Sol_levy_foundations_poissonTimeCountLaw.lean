-- Prove2me | solution 1 for levy_foundations_poissonTimeCountLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:32:18.215629+00:00
-- url     : https://prove2.me/submissions/05f5d19d-9f2b-46c2-b55b-e3487e7f08a6

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Poisson.Basic
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_poissonTimeCount
import Theorems.Thm_levy_foundations_prmCountLaw

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-! Poisson law for the time-space counting process, by the proved PRM law. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → ℝ × E) (A : Set E) (t : ℝ)
    (hd : LevyFoundations.IsPoissonPointFamily K X (volume.prod m) μ)
    (hA : MeasurableSet A) (hfin : m A < ⊤) (ht : 0 ≤ t) :
    μ.map (LevyFoundations.poissonTimeCount K X A t) =
      (poissonMeasure (ENNReal.ofReal t * m A).toNNReal).map
        (Nat.cast : ℕ → ℝ≥0∞) := by
  have hmass : (volume.prod m) (Set.Ioc 0 t ×ˢ A) =
      ENNReal.ofReal t * m A := by
    rw [Measure.prod_prod, Real.volume_Ioc]
    simp
  have hfin' : (volume.prod m) (Set.Ioc 0 t ×ˢ A) < ⊤ := by
    rw [hmass]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  have hmap := levy_foundations_prmCountLaw (volume.prod m) μ K X hd
    (measurableSet_Ioc.prod hA) hfin'
  change μ.map (fun ω => LevyFoundations.poissonRandomMeasure K X ω
    (Set.Ioc 0 t ×ˢ A)) =
      (poissonMeasure (ENNReal.ofReal t * m A).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞)
  simpa only [hmass] using hmap
