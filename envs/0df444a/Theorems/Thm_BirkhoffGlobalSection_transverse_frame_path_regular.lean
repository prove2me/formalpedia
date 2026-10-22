-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_transverse_frame_path_regular
-- name    : BirkhoffGlobalSection.transverse_frame_path_regular
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T20:13:47.304134+00:00
-- url     : https://prove2.me/theorems/8fdfb221-9020-404f-8215-f1ef5c1643bc
-- title:
--   Regularity of the ambient and frame comparison paths
-- statement:
--   Along a regular closed orbit, the two comparison paths are smooth and the frame path never vanishes. The ambient determinant path is smooth since the variational flow is $C^1$; the transverse frame-coordinate path of a level-tangent transverse vector is smooth; and transversality propagates because the linearized flow preserves level tangency and the Hamiltonian direction while the frame detects exactly the transverse directions.
--
--   This packages all regularity and propagation infrastructure used by the winding comparison, so that the comparison itself sees only well-behaved paths.
-- source:
--   Regularity and propagation for the quaternionic transverse frame versus the ambient determinant rotation; frame context of Joung-van Koert, https://arxiv.org/html/2407.19159v3, Section 2.3, determinant rotation map of Gutt, https://arxiv.org/pdf/1307.7239, p. 2, Theorem 1, Eq. (3).

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation

open scoped ContDiff

namespace BirkhoffGlobalSection

open scoped ContDiff

theorem transverse_frame_path_regular
    (F : Phase → ℝ) (S : Set Phase) (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn F S x T)
    (hregular : ∀ t : ℝ, ContDiffAt ℝ ∞ F (x t) ∧ fderiv ℝ F (x t) ≠ 0)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY : IsHamiltonianVariationalSolution F x Y)
    (v : Phase) (hv : fderiv ℝ F (x 0) v = 0)
    (htrans : transverseFrameCoordinates (TangentialHessian.grad F (x 0)) v ≠ 0)
    :
    ContDiffOn ℝ 1 (fun t => ambientRotationDet (Y t)) Set.univ ∧
      ContDiffOn ℝ 1
        (fun t => transverseFrameCoordinates (TangentialHessian.grad F (x t)) (Y t v))
        Set.univ ∧
      ∀ t : ℝ,
        transverseFrameCoordinates (TangentialHessian.grad F (x t)) (Y t v) ≠ 0 := by sorry

end BirkhoffGlobalSection
