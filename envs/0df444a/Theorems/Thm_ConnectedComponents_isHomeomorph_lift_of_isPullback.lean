-- Prove2me | Theorems.Thm_ConnectedComponents_isHomeomorph_lift_of_isPullback
-- name    : ConnectedComponents.isHomeomorph_lift_of_isPullback
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:16:54.86926+00:00
-- url     : https://prove2.me/theorems/65ba605f-34bc-5a36-9c2c-a500165182f0
-- title:
--   For a spectral space X and a profinite T over π₀(X), the fibre product Y has connected components homeomorphic to T
-- statement:
--   Let $X$ be a spectral space and $\pi_0(X)$ its space of connected components, with quotient map $\mathrm{mk}:X\to\pi_0(X)$. Let $T$ be a compact Hausdorff totally disconnected space (a profinite space) with a continuous map $i : T\to \pi_0(X)$, and let $Y$ be a topological space with continuous maps $f:Y\to X$ and $g:Y\to T$ such that the square
--   $$\begin{array}{ccc} Y & \xrightarrow{\;g\;} & T \\ {\scriptstyle f}\downarrow & & \downarrow{\scriptstyle i} \\ X & \xrightarrow{\;\mathrm{mk}\;} & \pi_0(X) \end{array}$$
--   is a pullback square in the category of topological spaces, i.e. $Y\cong T\times_{\pi_0(X)} X$. Then the map
--   $$\pi_0(Y) \longrightarrow T$$
--   induced by $g$ (which factors through $\pi_0(Y)$ because $T$ is totally disconnected) is a homeomorphism.
--
--   This is the first part of the Stacks Project lemma describing fibre products of a spectral space with a profinite space over its space of connected components; it controls the connected components of such fibre products, which arise when base-changing spectral spaces along profinite spaces over $\pi_0$.
--
--   **Formalization Note** `X Y T : Type u`, with `[SpectralSpace X]` and `[CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]`. The pullback is `IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)` in `TopCat`. The induced map is Mathlib's `Continuous.connectedComponentsLift g.2 : ConnectedComponents Y → T`, and the conclusion is `IsHomeomorph` of it.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014); cited in the code: Stacks Project, Tag 096C (first part). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/SpectralSpace/ConnectedComponent.lean, lines 368-376 (`ConnectedComponents.isHomeomorph_lift_of_isPullback`).

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Inseparable
import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Sober
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.Prespectral
import Definitions.Def_ProEtale_Mathlib_Topology_Category_TopCat_Limits_Pullbacks
import Definitions.Def_ProEtale_Mathlib_Topology_Connected_TotallyDisconnected
import Definitions.Def_ProEtale_Mathlib_Topology_Inseparable
import Definitions.Def_ProEtale_Mathlib_Topology_QuasiSeparated
import Definitions.Def_ProEtale_Mathlib_Topology_Separation_Hausdorff
import Definitions.Def_ProEtale_Mathlib_Topology_Sober
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Basic
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Prespectral
import Definitions.Def_ProEtale_Topology_Preliminaries_Profinite
import Definitions.Def_ProEtale_Topology_Preliminaries_Pullback
import Definitions.Def_ProEtale_Topology_SpectralSpace_ConnectedComponent

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe u

variable {X : Type u} [TopologicalSpace X]

section Spectral

variable [SpectralSpace X]

open CategoryTheory TopCat Continuous Limits

theorem ConnectedComponents.isHomeomorph_lift_of_isPullback {Y T : Type u} [TopologicalSpace Y]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    IsHomeomorph (connectedComponentsLift g.2) := by sorry

end Spectral
