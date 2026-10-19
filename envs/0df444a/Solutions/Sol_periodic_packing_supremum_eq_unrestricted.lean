-- Prove2me | solution 1 for periodic_packing_supremum_eq_unrestricted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/09f02565-a401-48d4-8811-c6deb622565e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SpherePacking_packing_supremum_eq_unit_separation
import Theorems.Thm_periodic_packing_supremum_eq_unit_separation
import Theorems.Thm_SpherePacking_exists_periodic_unit_packing_above_density_threshold

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise Topology
variable {d : ℕ}
theorem _root_.solution (hd : 0 < d) :
    PeriodicSpherePackingConstant d = SpherePackingConstant d := by
  rw [periodic_packing_supremum_eq_unit_separation (d := d),
    SpherePacking.packing_supremum_eq_unit_separation (d := d)]
  apply le_antisymm
  ·
    refine iSup₂_le ?_
    intro P hPsep
    refine
      (le_iSup
          (fun _ : (P.toSpherePacking).separation = 1 ↦ (P.toSpherePacking).upperPackingDensity)
          hPsep).trans ?_
    exact le_iSup (fun S : SpherePacking d ↦ ⨆ (_ : S.separation = 1), S.upperPackingDensity) P.toSpherePacking
  ·
    refine iSup₂_le ?_
    intro S hSsep
    refine le_of_forall_lt ?_
    intro a ha
    rcases exists_between ha with ⟨b, hab, hbS⟩
    rcases SpherePacking.exists_periodic_unit_packing_above_density_threshold
      (d := d) hd S hSsep hbS with
      ⟨P, hPsep, hbP⟩
    have hb_lt_sup : b < ⨆ (P : PeriodicSpherePacking d) (_ : P.separation = 1), P.upperPackingDensity :=
      lt_of_lt_of_le hbP (le_iSup_of_le P (le_iSup_of_le hPsep le_rfl))
    exact hab.trans hb_lt_sup
