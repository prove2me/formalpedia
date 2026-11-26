-- Prove2me | Theorems.Thm_CategoryTheory_IsPullback_compactSpace
-- name    : CategoryTheory.IsPullback.compactSpace
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:16:07.509886+00:00
-- url     : https://prove2.me/theorems/e9468e6e-f782-44a4-83a4-f0dbfa560d50
-- title:
--   A pullback of compact spaces over a Hausdorff space is compact
-- statement:
--   Let $X$, $Y$, $S$ be topological spaces with $S$ Hausdorff, let $f : X \to S$ and $g : Y \to S$ be continuous maps, and let $P$ be a topological space with continuous maps $g' : P \to X$ and $f' : P \to Y$ such that the square
--   $$\begin{array}{ccc} P & \xrightarrow{f'} & Y \\ {\scriptstyle g'}\downarrow & & \downarrow{\scriptstyle g} \\ X & \xrightarrow{f} & S \end{array}$$
--   is a pullback square in the category of topological spaces. If $X$ and $Y$ are compact, then $P$ is compact.
--
--   Indeed $P$ is homeomorphic to the fibre product $X \times_S Y$, which is a closed subspace of the compact space $X \times Y$ because $S$ is Hausdorff. The lemma is used to show that fibre products of profinite or spectral spaces arising in the pro-étale theory remain compact.
--
--   **Formalization Note** All spaces live in `Type u`; the pullback square is `IsPullback (ofHom g') (ofHom f') (ofHom f) (ofHom g)` in `TopCat`. Hausdorffness of $S$ is `[T2Space S]`, and compactness is `CompactSpace`. The theorem is `CategoryTheory.IsPullback.compactSpace`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Preliminaries/Pullback.lean, lines 65-66 (`CategoryTheory.IsPullback.compactSpace`).

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Inseparable
import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sober
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.Prespectral
import Definitions.Def_ProEtale_Mathlib_Topology_Category_TopCat_Limits_Pullbacks
import Definitions.Def_ProEtale_Mathlib_Topology_Inseparable
import Definitions.Def_ProEtale_Mathlib_Topology_QuasiSeparated
import Definitions.Def_ProEtale_Mathlib_Topology_Separation_Hausdorff
import Definitions.Def_ProEtale_Mathlib_Topology_Sober
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Basic
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Prespectral
import Definitions.Def_ProEtale_Topology_Preliminaries_Pullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe u

open CategoryTheory TopCat Limits

variable {X Y S : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace S]
variable (f : C(X, S)) (g : C(Y, S))

variable {P : Type u} [TopologicalSpace P] {f' : C(P, Y)} {g' : C(P, X)}
    (pb : IsPullback (ofHom g') (ofHom f') (ofHom f) (ofHom g))

section IsPullback

variable {f g}

include f' g' pb

variable [T2Space S]

theorem CategoryTheory.IsPullback.compactSpace [CompactSpace X] [CompactSpace Y] : CompactSpace P := by sorry

end IsPullback
