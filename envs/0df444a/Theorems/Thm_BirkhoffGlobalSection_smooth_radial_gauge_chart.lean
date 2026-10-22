-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_smooth_radial_gauge_chart
-- name    : BirkhoffGlobalSection.smooth_radial_gauge_chart
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-30T17:59:27.899676+00:00
-- url     : https://prove2.me/theorems/cac241c3-aed1-4423-b740-7f890823f4e8
-- title:
--   A smooth radial gauge chart for a convex energy boundary
-- statement:
--   Let B be a convex, von Neumann bounded neighborhood of zero in four-dimensional real phase space, and let F be a real-valued function that is smooth at every point of the frontier of B. Assume F vanishes on that frontier and its radial derivative satisfies $DF_y(y)\ne 0$ at each frontier point y. Let g_B be the Minkowski gauge of B, let N(y)=y/sqrt(sum_i y_i^2), and put
--
--   $$G(u)=\frac{u}{g_B(u)}.$$
--
--   $$G(N(y))=y\quad(y\in\partial B),\qquad N(G(u))=u\quad(u\in S^3).$$
--
--   Both N and G are smooth at points of their respective boundary and sphere domains, N maps the frontier to the coordinate Euclidean unit sphere, and G maps the sphere to the frontier. Thus these formulas provide smooth inverse parametrizations of the two surfaces. The assumptions concern only the frontier: the whole zero set of F need not equal it.
--
--   This chart is the geometric coordinate step needed to transport Hamiltonian characteristic dynamics to the standard sphere. Contact nondegeneracy, a complete Reeb clock, winding-index compatibility and global sections are separate assertions.
-- source:
--   Auxiliary gauge-based version of the star-shaped smooth sphere correspondence in Hryniewicz, arXiv:1105.2077v5, p. 2, https://arxiv.org/pdf/1105.2077. Uses Mathlib gauge_eq_one_iff_mem_frontier, gauge_pos and continuous_gauge in Analysis/Convex/Gauge.lean, and ContDiffAt.eventually_apply_eq_iff_implicitFunction and ContDiffAt.contDiffAt_implicitFunction in Analysis/Calculus/ImplicitContDiff.lean, at revision 0df444a360eaa60ab8c11dca51a86af692955474. This is an auxiliary theorem with explicit smoothness and nonzero radial derivative hypotheses, not a verbatim source theorem.

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel
import Theorems.Thm_BirkhoffGlobalSection_radial_normalization_contact_identity
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Calculus.ImplicitContDiff
open scoped ContDiff Topology
open BirkhoffGlobalSection Filter Set

theorem BirkhoffGlobalSection.smooth_radial_gauge_chart
    (B : Set Phase) (hc : Convex ℝ B) (h0 : B ∈ 𝓝 (0 : Phase))
    (hb : Bornology.IsVonNBounded ℝ B) (F : Phase → ℝ)
    (hzero : ∀ y ∈ frontier B, F y = 0)
    (hsmooth : ∀ y ∈ frontier B, ContDiffAt ℝ ∞ F y)
    (hrad : ∀ y ∈ frontier B, fderiv ℝ F y y ≠ 0) :
    let G : Phase → Phase := fun u => (gauge B u)⁻¹ • u
    (∀ y ∈ frontier B,
      ContDiffAt ℝ ∞ radialNormalize y ∧ radialNormalize y ∈ unitThreeSphere ∧
        G (radialNormalize y) = y) ∧
    (∀ u ∈ unitThreeSphere,
      ContDiffAt ℝ ∞ G u ∧ G u ∈ frontier B ∧ radialNormalize (G u) = u) := by sorry
