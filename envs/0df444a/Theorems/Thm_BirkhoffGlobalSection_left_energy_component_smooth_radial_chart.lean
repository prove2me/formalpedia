-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_energy_component_smooth_radial_chart
-- name    : BirkhoffGlobalSection.left_energy_component_smooth_radial_chart
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T21:26:09.111633+00:00
-- url     : https://prove2.me/theorems/5f723e28-54eb-4ef6-9864-922f93317eb1
-- title:
--   Smooth odd radial chart for the subcritical Levi-Civita component
-- statement:
--   For every mass parameter $0<\mu<1$ and energy below the first critical value, radial normalization of the selected Levi-Civita component has a smooth ambient representative of its inverse. There is a map $G:\mathbb R^4\to\mathbb R^4$, smooth at every point of the unit three-sphere, such that
--
--   $$G(S^3)\subset\Sigma_{\mu,c},\qquad N(G(u))=u,\qquad G(N(y))=y\quad(y\in\Sigma_{\mu,c}).$$
--
--   Moreover $G(-u)=-G(u)$ on $S^3$, and for each unit $u$ there is a positive radius $r$ with $G(u)=ru$. Thus this is the odd smooth radial chart, rather than merely a topological identification of the component with a sphere. No behavior at the origin is required.
-- source:
--   Derived smooth refinement of the star-shaped radial sphere model in Joung--van Koert, Proposition2.4, and the proved source ray uniqueness and radial derivative positivity statements. The formal proof uses compact_unique_ray_radial_graph, Tietze extension, and Mathlib Analysis/Calculus/ImplicitContDiff.lean (ContDiffAt.implicitFunction and eventual local uniqueness) to upgrade a continuous radius to a smooth one. It generalizes the implicit-radius argument from accepted smooth_radial_gauge_chart, submission0a6b8288-05d8-46ac-bf13-6e10d532f4ed, https://prove2.me/theorems/cac241c3-aed1-4423-b740-7f890823f4e8. Supporting geometric chart for https://prove2.me/theorems/f7c5a998-6bbc-4ef2-a169-fabd06647d10; this is a derived lemma, not a verbatim numbered source statement.

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf
open BirkhoffGlobalSection
open scoped ContDiff

theorem BirkhoffGlobalSection.left_energy_component_smooth_radial_chart
    (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hc : belowFirstCriticalValue μ c) :
    ∃ G : Phase → Phase,
      (∀ u ∈ unitThreeSphere, ContDiffAt ℝ ∞ G u ∧ G u ∈ leftEnergyComponent μ c ∧
        radialNormalize (G u) = u ∧ G (-u) = -G u ∧ ∃ r : ℝ, 0 < r ∧ G u = r • u) ∧
      (∀ y ∈ leftEnergyComponent μ c, G (radialNormalize y) = y) := by sorry
