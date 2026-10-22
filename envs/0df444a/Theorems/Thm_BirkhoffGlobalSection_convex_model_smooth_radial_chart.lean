-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_model_smooth_radial_chart
-- name    : BirkhoffGlobalSection.convex_model_smooth_radial_chart
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T00:24:07.218707+00:00
-- url     : https://prove2.me/theorems/2dadc612-f8da-4682-bd46-5ec7dce3101c
-- title:
--   Model fields supply the smooth radial chart without contact positivity
-- statement:
--   For any ConvexRegularizationModel M, radial normalization and the inverse gauge map G(u)=g_{M.body}(u)^{-1}u are smooth inverse surface maps between its body frontier and the coordinate unit three-sphere. Explicitly, every boundary y has smooth radial normalization lying on the sphere with G(radialNormalize(y))=y, and every sphere point u has G smooth at u, G(u) on the frontier, and radialNormalize(G(u))=u. No contact-positivity hypothesis is supplied: the model regularity and convexity imply radial transversality.
-- source:
--   Original auxiliary convex-boundary derivation in real four-dimensional Phase, using Mathlib Hahn--Banach separation (Analysis/LocallyConvex/Separation.lean), local extrema, gauge and implicit-function lemmas at revision 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis. The local inverse-gauge argument adapts the accepted BirkhoffGlobalSection.smooth_radial_gauge_chart proof (cac241c3-aed1-4423-b740-7f890823f4e8). This is an auxiliary derivation, not a verbatim theorem of Joung--van Koert or Hryniewicz.

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel
import Definitions.Def_BirkhoffGlobalSection_TransverseHopf
import Mathlib.Analysis.Convex.GaugeRescale

open BirkhoffGlobalSection Filter Set
open scoped ContDiff Topology

theorem BirkhoffGlobalSection.convex_model_smooth_radial_chart {μ c : ℝ} (M : ConvexRegularizationModel μ c) :
    let G : Phase → Phase := fun u => (gauge M.body u)⁻¹ • u
    (∀ y ∈ frontier M.body,
      ContDiffAt ℝ ∞ radialNormalize y ∧ radialNormalize y ∈ unitThreeSphere ∧
        G (radialNormalize y) = y) ∧
    (∀ u ∈ unitThreeSphere,
      ContDiffAt ℝ ∞ G u ∧ G u ∈ frontier M.body ∧ radialNormalize (G u) = u) := by sorry
