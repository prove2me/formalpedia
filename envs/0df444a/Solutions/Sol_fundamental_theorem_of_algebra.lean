-- Prove2me | solution 1 for fundamental_theorem_of_algebra
-- status  : ACCEPTED   (sketch)
-- author  : @Henry Yuen
-- created : 2026-05-22T14:59:24.397787+00:00
-- url     : https://prove2.me/submissions/c1b5c010-81f9-4297-bf90-1a70f25b7c23

import Definitions.Def_fta_winding_infra
import Theorems.Thm_fta_polynomial_large_circle_dominates
import Theorems.Thm_fta_winding_rootless_boundary_has_lift
import Theorems.Thm_fta_winding_homotopy_preserves_lift
import Theorems.Thm_fta_winding_large_circle_homotopic_to_leading
import Theorems.Thm_fta_winding_power_loop_no_lift
import Mathlib.Analysis.Complex.Polynomial.Basic

theorem solution (f : Polynomial ℂ) (hf : 0 < f.degree) :
    ∃ z : ℂ, f.IsRoot z := by
  by_contra hnoroot
  have hrootless_all : ∀ z : ℂ, ¬ f.IsRoot z := by
    intro z hz
    exact hnoroot ⟨z, hz⟩
  obtain ⟨R, hR, hdom⟩ := fta_polynomial_large_circle_dominates f hf
  have hclosed : FtaClosedDiskRootless f R := by
    intro z _hz
    exact hrootless_all z
  have hboundary_lift : FtaHasLift (FtaBoundaryLoop f R) :=
    fta_winding_rootless_boundary_has_lift f R hR hclosed
  have hhom :
      FtaCircleHomotopic (FtaBoundaryLoop f R)
        (FtaLeadingLoop (FtaLeadingCoeffCircle f) f.natDegree) :=
    fta_winding_large_circle_homotopic_to_leading f R hR hdom
  have hleading_lift :
      FtaHasLift (FtaLeadingLoop (FtaLeadingCoeffCircle f) f.natDegree) :=
    fta_winding_homotopy_preserves_lift
      (FtaBoundaryLoop f R)
      (FtaLeadingLoop (FtaLeadingCoeffCircle f) f.natDegree)
      hhom hboundary_lift
  have hn : 0 < f.natDegree := by
    rwa [Polynomial.natDegree_pos_iff_degree_pos]
  exact (fta_winding_power_loop_no_lift (FtaLeadingCoeffCircle f) f.natDegree hn) hleading_lift
