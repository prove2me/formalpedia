-- Prove2me | solution 1 for d9_hasDerivWithinAt_integral_of_slope_dct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T12:45:11.480316+00:00
-- url     : https://prove2.me/submissions/838166c3-6564-49cf-8cf8-af5b855b6301

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy
open scoped Topology
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℝ → Ω → ℝ) (G : ℝ → ℝ) (D : Ω → ℝ)
    (B s : ℝ)
    (hG : ∀ t, G t = ∫ ω, F t ω ∂P)
    (hFInt : ∀ t, s ≤ t → Integrable (F t) P)
    (hSlopeInt : ∀ t, s ≤ t →
      Integrable (fun ω => slope (fun u => F u ω) s t) P)
    (hSlopeBound : ∀ t, s ≤ t → ∀ ω,
      ‖slope (fun u => F u ω) s t‖ ≤ B)
    (hDeriv : ∀ ω, HasDerivWithinAt (fun t => F t ω) (D ω)
      (Set.Ici s) s)
    (hB : Integrable (fun _ : Ω => B) P) :
    HasDerivWithinAt G (∫ ω, D ω ∂P) (Set.Ici s) s := by
  let l : Filter ℝ := 𝓝[Set.Ici s \ {s}] s
  have hmeas : ∀ᶠ t in l,
      AEStronglyMeasurable (fun ω => slope (fun u => F u ω) s t) P := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change t ∈ Set.Ici s ∧ t ∉ ({s} : Set ℝ) at ht
    have hst : s ≤ t := Set.mem_Ici.mp ht.1
    exact (hSlopeInt t hst).aestronglyMeasurable
  have hbound : ∀ᶠ t in l, ∀ᵐ ω ∂P,
      ‖slope (fun u => F u ω) s t‖ ≤ B := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change t ∈ Set.Ici s ∧ t ∉ ({s} : Set ℝ) at ht
    have hst : s ≤ t := Set.mem_Ici.mp ht.1
    filter_upwards [] with ω
    exact hSlopeBound t hst ω
  have hlim : ∀ᵐ ω ∂P,
      Filter.Tendsto (fun t => slope (fun u => F u ω) s t) l (𝓝 (D ω)) := by
    filter_upwards [] with ω
    exact (hasDerivWithinAt_iff_tendsto_slope.mp (hDeriv ω))
  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : Ω => B) hmeas hbound hB hlim
  have hEq : (fun t => ∫ ω, slope (fun u => F u ω) s t ∂P) =ᶠ[l]
      (fun t => slope G s t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change t ∈ Set.Ici s ∧ t ∉ ({s} : Set ℝ) at ht
    have hst : s ≤ t := Set.mem_Ici.mp ht.1
    have hne : s ≠ t := by
      intro heq
      subst t
      exact ht.2 (by simp)
    simp only [slope_def_field, div_eq_mul_inv]
    rw [show (fun ω =>
        (F t ω - F s ω) * (t - s)⁻¹) =
        (fun ω => (t - s)⁻¹ * (F t ω - F s ω)) by
      funext ω
      ring]
    rw [integral_const_mul, integral_sub (hFInt t hst) (hFInt s le_rfl)]
    simp only [hG]
    ring
  have hSlope : Filter.Tendsto (fun t => slope G s t) l
      (𝓝 (∫ ω, D ω ∂P)) := hDCT.congr' hEq
  exact hasDerivWithinAt_iff_tendsto_slope.mpr hSlope
