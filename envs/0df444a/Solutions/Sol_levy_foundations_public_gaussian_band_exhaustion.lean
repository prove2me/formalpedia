-- Prove2me | solution 1 for levy_foundations_public_gaussian_band_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T10:30:27.602206+00:00
-- url     : https://prove2.me/submissions/6b1a9fa7-7918-4b99-ba08-16300168817a

import Mathlib.Probability.Independence.CharacteristicFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology

/-- Dominated convergence on shrinking annuli transfers a uniform quadratic
bound to the full ball when the measure has no atom at zero. -/
theorem solution
    (ν : Measure ℝ) {r σ : ℝ}
    (hν_zero : ν {0} = 0)
    (hquad : IntegrableOn (fun x : ℝ => x ^ 2) {x | |x| < r} ν)
    {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (nhds (0 : ℝ)))
    (hband : ∀ m, ∫ x in {x | δ m ≤ |x| ∧ |x| < r}, x ^ 2 ∂ν ≤ σ) :
    ∫ x in {x | |x| < r}, x ^ 2 ∂ν ≤ σ := by
  set f : ℕ → ℝ → ℝ := fun m x =>
    Set.indicator {x : ℝ | δ m ≤ |x| ∧ |x| < r} (fun x => x ^ 2) x with hf_def
  have h_meas_ball : MeasurableSet {x : ℝ | |x| < r} :=
    (isOpen_lt continuous_abs continuous_const).measurableSet
  have h_meas_band : ∀ m, MeasurableSet {x : ℝ | δ m ≤ |x| ∧ |x| < r} :=
    fun m => (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  have h_band_int : ∀ m,
      ∫ x in {x | δ m ≤ |x| ∧ |x| < r}, x ^ 2 ∂ν = ∫ x, f m x ∂ν :=
    fun m => (integral_indicator (h_meas_band m)).symm
  have h_ball_int : ∫ x in {x | |x| < r}, x ^ 2 ∂ν =
      ∫ x, Set.indicator {x : ℝ | |x| < r} (fun x => x ^ 2) x ∂ν :=
    (integral_indicator h_meas_ball).symm
  have h_lim : Tendsto (fun m => ∫ x, f m x ∂ν) atTop
      (nhds (∫ x, Set.indicator {x : ℝ | |x| < r} (fun x => x ^ 2) x ∂ν)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (bound := fun x => Set.indicator {x : ℝ | |x| < r} (fun x => x ^ 2) x)
      (fun m => ((continuous_pow 2).aestronglyMeasurable.indicator (h_meas_band m)))
      ?_ ?_ ?_
    · exact (integrable_indicator_iff h_meas_ball).mpr hquad
    · intro m
      refine Filter.Eventually.of_forall (fun x => ?_)
      simp only [Real.norm_eq_abs, hf_def, Set.indicator_apply]
      by_cases hx : x ∈ {x : ℝ | δ m ≤ |x| ∧ |x| < r}
      · have hxr : x ∈ {x : ℝ | |x| < r} := hx.2
        rw [if_pos hx, if_pos hxr]
        exact le_of_eq (abs_of_nonneg (sq_nonneg x))
      · rw [if_neg hx]
        simp only [abs_zero]
        split <;> [exact sq_nonneg x; exact le_refl 0]
    · have h_ae : ∀ᵐ x ∂ν, x ≠ 0 := by
        rw [ae_iff]
        simpa using hν_zero
      filter_upwards [h_ae] with x hx0
      by_cases hxr : x ∈ {x : ℝ | |x| < r}
      · rw [Set.indicator_of_mem hxr]
        have hx_pos : 0 < |x| := abs_pos.mpr hx0
        have h_ev : ∀ᶠ m in atTop, δ m < |x| :=
          hδ.eventually_lt_const hx_pos
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [h_ev] with m hm
        have hmem : x ∈ {x : ℝ | δ m ≤ |x| ∧ |x| < r} :=
          ⟨le_of_lt hm, hxr⟩
        simp only [hf_def, Set.indicator_apply, if_pos hmem]
      · rw [Set.indicator_of_notMem hxr]
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        refine Filter.Eventually.of_forall (fun m => ?_)
        have hnmem : x ∉ {x : ℝ | δ m ≤ |x| ∧ |x| < r} :=
          fun h => hxr h.2
        simp only [hf_def, Set.indicator_apply, if_neg hnmem]
  rw [h_ball_int]
  exact le_of_tendsto' (h_lim.congr (fun m => (h_band_int m).symm)) hband
