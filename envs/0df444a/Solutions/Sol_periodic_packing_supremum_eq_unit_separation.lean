-- Prove2me | solution 1 for periodic_packing_supremum_eq_unit_separation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/ded5b56b-c1fd-4771-8624-94e817b354a5

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SpherePacking_rescale_upper_packing_density

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
theorem _root_.solution :
    PeriodicSpherePackingConstant d = ⨆ (S : PeriodicSpherePacking d) (_ : S.separation = 1),
    S.upperPackingDensity := by
  rw [iSup_subtype', PeriodicSpherePackingConstant]
  apply le_antisymm
  · apply iSup_le
    intro S
    have h := inv_mul_cancel₀ S.separation_pos.ne.symm
    have := le_iSup (fun x : { x : PeriodicSpherePacking d // x.separation = 1 } ↦ x.val.upperPackingDensity)
        ⟨S.rescaleConfiguration (inv_pos.mpr S.separation_pos), h⟩
    rw [← rescale_upper_packing_density]
    · exact this
    · rw [inv_pos]
      exact S.separation_pos
  · refine iSup_le ?_
    rintro ⟨S, _⟩
    exact le_iSup (fun S : PeriodicSpherePacking d => S.upperPackingDensity) S
