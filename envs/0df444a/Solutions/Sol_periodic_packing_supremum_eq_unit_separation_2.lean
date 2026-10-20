-- Prove2me | solution 2 for periodic_packing_supremum_eq_unit_separation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:00:03.781506+00:00
-- url     : https://prove2.me/submissions/9c71e5c4-2e24-4816-89cf-eb755b319060

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open Filter
open scoped Pointwise
open scoped Topology
variable {d : ℕ}
theorem h48_rescale_upper (S : SpherePacking d) {c : ℝ} (hc : 0 < c) :
    (S.rescaleConfiguration hc).upperPackingDensity = S.upperPackingDensity := by
  unfold SpherePacking.upperPackingDensity
  have hf : (S.rescaleConfiguration hc).densityInsideRadius =
      S.densityInsideRadius ∘ (fun R : ℝ => R / c) := by
    funext R
    exact rescale_local_packing_density_radius S hc R
  rw [hf, Filter.limsup_comp, Filter.map_div_atTop_eq c hc]

theorem solution :
    PeriodicSpherePackingConstant d = ⨆ (S : PeriodicSpherePacking d) (_ : S.separation = 1),
    S.upperPackingDensity := by
  apply le_antisymm
  · unfold PeriodicSpherePackingConstant
    refine iSup_le fun S => ?_
    have hc : 0 < S.separation⁻¹ := inv_pos.mpr S.separation_pos
    have hsep : (S.rescaleConfiguration hc).separation = 1 := by
      change S.separation⁻¹ * S.separation = 1
      exact inv_mul_cancel₀ S.separation_pos.ne'
    refine le_iSup₂_of_le (f := fun (S : PeriodicSpherePacking d) (_ : S.separation = 1) =>
      S.upperPackingDensity) (S.rescaleConfiguration hc) hsep (le_of_eq ?_)
    exact (h48_rescale_upper S.toSpherePacking hc).symm
  · exact iSup₂_le fun S _ => le_iSup (fun S : PeriodicSpherePacking d => S.upperPackingDensity) S

