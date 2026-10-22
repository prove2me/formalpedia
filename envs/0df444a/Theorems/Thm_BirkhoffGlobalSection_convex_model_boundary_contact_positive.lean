-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_boundary_contact_positive
-- name    : BirkhoffGlobalSection.convex_model_boundary_contact_positive
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T00:23:51.84256+00:00
-- url     : https://prove2.me/theorems/ab6a114a-3163-4c34-a9fa-bb58db0a5619
-- title:
--   Convex regularization models have positive boundary contact pairing
-- statement:
--   For any ConvexRegularizationModel M, every boundary point y of its compact convex body satisfies
--
--   $$\alpha_y(X_{H_M}(y))>0,$$
--
--   where alpha is the workspace radial primitive and X_{H_M} its Hamiltonian vector field. This follows from the model fields: the origin is interior, the Hamiltonian is smooth and regular on the zero frontier, and its tangential Hessian is positive. There is no additional sign hypothesis. This result does not assert existence of a model or a global surface of section.
-- source:
--   Original auxiliary convex-boundary derivation in real four-dimensional Phase, using Mathlib Hahn--Banach separation (Analysis/LocallyConvex/Separation.lean), local extrema, gauge and implicit-function lemmas at revision 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis. The local inverse-gauge argument adapts the accepted BirkhoffGlobalSection.smooth_radial_gauge_chart proof (cac241c3-aed1-4423-b740-7f890823f4e8). This is an auxiliary derivation, not a verbatim theorem of Joung--van Koert or Hryniewicz.

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel
import Definitions.Def_BirkhoffGlobalSection_TransverseHopf

open BirkhoffGlobalSection Filter Set
open scoped ContDiff Topology

theorem BirkhoffGlobalSection.convex_model_boundary_contact_positive {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) :
    ∀ y ∈ frontier M.body,
      0 < phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y) := by sorry
