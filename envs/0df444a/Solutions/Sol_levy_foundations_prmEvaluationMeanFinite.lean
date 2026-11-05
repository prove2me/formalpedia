-- Prove2me | solution 1 for levy_foundations_prmEvaluationMeanFinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:57:08.262506+00:00
-- url     : https://prove2.me/submissions/5e5619f8-4fda-400a-a0d6-6fea6351f951

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Probability.Distributions.Poisson.Basic
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_poissonRandomMeasure
import Theorems.Thm_levy_foundations_prmCountLaw
import Theorems.Thm_levy_foundations_measurablePRMEval
import Theorems.Thm_ProbabilityTheory_leanlevy_lintegral_id_poissonMeasure

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
    {A : Set E} (hA : MeasurableSet A) (hfin : m A < ⊤) :
    ∫⁻ ω, LevyFoundations.poissonRandomMeasure K X ω A ∂μ = m A := by
  let F : Ω → ENNReal := fun ω => LevyFoundations.poissonRandomMeasure K X ω A
  have hF : Measurable F :=
    levy_foundations_measurablePRMEval K X hd.measurable_count hd.measurable_point hA
  have hlaw : μ.map F =
      (poissonMeasure (m A).toNNReal).map (Nat.cast : ℕ → ENNReal) :=
    levy_foundations_prmCountLaw m μ K X hd hA hfin
  change ∫⁻ ω, F ω ∂μ = m A
  calc
    ∫⁻ ω, F ω ∂μ = ∫⁻ y : ENNReal, y ∂(μ.map F) :=
      (lintegral_map measurable_id hF).symm
    _ = ∫⁻ n : ℕ, (n : ENNReal) ∂(poissonMeasure (m A).toNNReal) := by
      rw [hlaw]
      exact lintegral_map measurable_id
        (show Measurable (Nat.cast : ℕ → ENNReal) from measurable_from_top)
    _ = m A := by
      rw [ProbabilityTheory.leanlevy_lintegral_id_poissonMeasure]
      exact ENNReal.coe_toNNReal hfin.ne
