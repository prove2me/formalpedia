-- Prove2me | solution 1 for levy_foundations_existsCompensatedPoissonL2Extension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:47:55.895192+00:00
-- url     : https://prove2.me/submissions/430e11a3-9441-4f68-bc35-703b8206144e

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Probability.ConditionalProbability
import Mathlib.Topology.Instances.RealVectorSpace
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_isCompensatedPoissonL2Extension
import Theorems.Thm_ProbabilityTheory_integral_compensatedPoissonIntegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

/-- Construct the compensated L² integral as a continuous additive isometry. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ) :
    ∃ I : Lp ℝ 2 m → Lp ℝ 2 μ,
      LevyFoundations.IsCompensatedPoissonL2Extension m μ K X I := by
  let hd' : ProbabilityTheory.IsPoissonPointFamily K X m μ :=
    ⟨hd.measurable_count, hd.measurable_point, hd.indep, hd.law_count, hd.law_point⟩
  let I : Lp ℝ 2 m → Lp ℝ 2 μ :=
    ProbabilityTheory.compensatedPoissonIntegral hd'
  have hadd : ∀ f g : Lp ℝ 2 m, I (f + g) = I f + I g :=
    fun f g => ProbabilityTheory.compensatedPoissonIntegral_add hd' f g
  have hnorm : ∀ f : Lp ℝ 2 m, ‖I f‖ = ‖f‖ :=
    fun f => ProbabilityTheory.norm_compensatedPoissonIntegral hd' f
  let F : Lp ℝ 2 m →+ Lp ℝ 2 μ :=
    { toFun := I
      map_zero' := by
        apply norm_eq_zero.mp
        simpa using hnorm (0 : Lp ℝ 2 m)
      map_add' := hadd }
  have hcont : Continuous (F : Lp ℝ 2 m → Lp ℝ 2 μ) := by
    have hiso : Isometry F := by
      apply (isometry_iff_dist_eq).2
      intro f g
      calc
        dist (F f) (F g) = ‖F f - F g‖ := dist_eq_norm _ _
        _ = ‖F (f - g)‖ := by rw [map_sub]
        _ = ‖f - g‖ := hnorm _
        _ = dist f g := (dist_eq_norm _ _).symm
    exact hiso.continuous
  refine ⟨I, ?_⟩
  refine ⟨hadd, ?_, hnorm, ?_, ?_⟩
  · intro c f
    change F (c • f) = c • F f
    exact map_real_smul F hcont c f
  · intro f
    exact ProbabilityTheory.integral_compensatedPoissonIntegral hd' f
  · intro f hf hf1 hf2
    change (fun ω => ProbabilityTheory.compensatedPoissonIntegral hd' (hf2.toLp f) ω)
      =ᵐ[μ] ProbabilityTheory.compensatedPoissonSum K X f m
    exact ProbabilityTheory.compensatedPoissonIntegral_eq_sum hd' hf hf1 hf2
