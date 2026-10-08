-- Prove2me | solution 1 for d9_hasDerivWithinAt_integral_of_slope_dct_left
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T11:05:26.448981+00:00
-- url     : https://prove2.me/submissions/fbb0d1c4-de7b-45d4-a9e0-61ab9f907703

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open NestedSeatAlloc.IntPolicy
open scoped Topology

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℝ → Ω → ℝ) (G : ℝ → ℝ) (D : Ω → ℝ)
    (B s : ℝ) (hs : 0 < s)
    (hG : ∀ t, G t = ∫ ω, F t ω ∂P)
    (hFInt : ∀ t, 0 ≤ t → t ≤ s → Integrable (F t) P)
    (hSlopeInt : ∀ t, 0 ≤ t → t ≤ s →
      Integrable (fun ω => slope (fun u => F u ω) s t) P)
    (hSlopeBound : ∀ t, 0 ≤ t → t ≤ s → ∀ ω,
      ‖slope (fun u => F u ω) s t‖ ≤ B)
    (hDeriv : ∀ ω, HasDerivWithinAt (fun t => F t ω) (D ω)
      (Set.Iic s) s)
    (hB : Integrable (fun _ : Ω => B) P) :
    HasDerivWithinAt G (∫ ω, D ω ∂P) (Set.Iic s) s := by
  let l : Filter ℝ := 𝓝[Set.Iic s \ {s}] s
  have hpos : ∀ᶠ t in l, 0 < t := by
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hs)
  have hmeas : ∀ᶠ t in l,
      AEStronglyMeasurable (fun ω => slope (fun u => F u ω) s t) P := by
    filter_upwards [self_mem_nhdsWithin, hpos] with t ht ht0
    change t ≤ s ∧ t ≠ s at ht
    exact (hSlopeInt t (le_of_lt ht0) ht.1).aestronglyMeasurable
  have hbound : ∀ᶠ t in l, ∀ᵐ ω ∂P,
      ‖slope (fun u => F u ω) s t‖ ≤ B := by
    filter_upwards [self_mem_nhdsWithin, hpos] with t ht ht0
    change t ≤ s ∧ t ≠ s at ht
    filter_upwards [] with ω
    exact hSlopeBound t (le_of_lt ht0) ht.1 ω
  have hlim : ∀ᵐ ω ∂P,
      Filter.Tendsto (fun t => slope (fun u => F u ω) s t) l (𝓝 (D ω)) := by
    filter_upwards [] with ω
    exact (hasDerivWithinAt_iff_tendsto_slope.mp (hDeriv ω))
  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : Ω => B) hmeas hbound hB hlim
  have hEq : (fun t => ∫ ω, slope (fun u => F u ω) s t ∂P) =ᶠ[l]
      (fun t => slope G s t) := by
    filter_upwards [self_mem_nhdsWithin, hpos] with t ht ht0
    change t ≤ s ∧ t ≠ s at ht
    have hts : t ≤ s := ht.1
    have hne : s ≠ t := Ne.symm ht.2
    simp only [slope_def_field, div_eq_mul_inv]
    rw [show (fun ω =>
        (F t ω - F s ω) * (t - s)⁻¹) =
        (fun ω => (t - s)⁻¹ * (F t ω - F s ω)) by
      funext ω
      ring]
    rw [integral_const_mul,
      integral_sub (hFInt t (le_of_lt ht0) hts)
        (hFInt s (le_of_lt hs) le_rfl)]
    simp only [hG]
    ring
  have hSlope : Filter.Tendsto (fun t => slope G s t) l
      (𝓝 (∫ ω, D ω ∂P)) := hDCT.congr' hEq
  exact hasDerivWithinAt_iff_tendsto_slope.mpr hSlope
