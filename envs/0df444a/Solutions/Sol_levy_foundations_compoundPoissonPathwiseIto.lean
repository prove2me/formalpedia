-- Prove2me | solution 1 for levy_foundations_compoundPoissonPathwiseIto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:04:32.041852+00:00
-- url     : https://prove2.me/submissions/0a46a1c3-7fe4-4896-85c8-5b3044667bf9

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Exponential
import Definitions.Def_levy_foundations_isCadlag
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_piecewisePath
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Theorems.Thm_levy_foundations_piecewisePathIto
import Theorems.Thm_levy_foundations_compoundDriverArrivalDiverges
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal Interval

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {b : ℝ} {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0}
    {ν' : Measure ℝ} {μ : Measure Ω} (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f') :
    ∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t →
      f (LevyFoundations.compoundPoisson b τ Y t ω) -
        f (LevyFoundations.compoundPoisson b τ Y 0 ω) =
      (∫ s in (0:ℝ)..t, f' (LevyFoundations.compoundPoisson b τ Y s ω) * b) +
      ∑ n ∈ Finset.range (LevyFoundations.jumpCount
          (fun m => LevyFoundations.arrival τ m ω) t),
        (f (LevyFoundations.compoundPoisson b τ Y (LevyFoundations.arrival τ n ω) ω) -
         f (LevyFoundations.compoundPoisson b τ Y (LevyFoundations.arrival τ n ω) ω - Y n ω)) := by
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  haveI : IsProbabilityMeasure (expMeasure (r : ℝ)) :=
    isProbabilityMeasure_expMeasure hr'
  have hτpos : ∀ᵐ ω ∂μ, ∀ n, 0 < τ n ω := by
    rw [ae_all_iff]
    intro n
    rw [ae_iff]
    have hset : {ω | ¬ 0 < τ n ω} = (τ n) ⁻¹' Set.Iic 0 := by
      ext ω
      simp [Set.mem_Iic, not_lt]
    rw [hset, ← Measure.map_apply (hd.measurable_interarrival n) measurableSet_Iic,
      (hd.law_interarrival n).map_eq, ← ofReal_cdf (expMeasure (r : ℝ)) 0,
      cdf_expMeasure_eq hr' 0]
    simp
  filter_upwards [hτpos, levy_foundations_compoundDriverArrivalDiverges hd hr]
    with ω hpos htop
  have hmono : StrictMono (fun n => LevyFoundations.arrival τ n ω) := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    change (∑ i ∈ Finset.range (n + 1), τ i ω) <
      (∑ i ∈ Finset.range ((n + 1) + 1), τ i ω)
    conv_rhs => rw [Finset.sum_range_succ]
    exact lt_add_of_pos_right _ (hpos (n + 1))
  have hfirst : 0 < LevyFoundations.arrival τ 0 ω := by
    simpa [LevyFoundations.arrival] using hpos 0
  intro t ht
  simpa only [LevyFoundations.compoundPoisson] using
    (levy_foundations_piecewisePathIto (x₀ := 0) (b := b)
      (T := fun n => LevyFoundations.arrival τ n ω)
      (Y := fun n => Y n ω) hf hf' hmono htop hfirst ht)
