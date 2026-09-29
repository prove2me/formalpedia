-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_iso_of_map_eq_smul_of_map_eq_smul
-- name    : AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_iso_of_map_eq_smul_of_map_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/5bb977b3-d1b1-5ee2-bb66-a84495dbeb98
-- title:
--   Gluing two frames: modules with equal transition function are isomorphic
-- statement:
--   Let $X$ be a scheme and let $L$, $L'$ be objects of $X.\mathrm{Modules}$, the category of $\mathcal{O}_X$-module presheaves used throughout. Let $U, V$ be open subsets of $X$ with $U \sqcup V = \top$, i.e. covering $X$. Assume given sections $s_U \in \Gamma(L, U)$ and $s_V \in \Gamma(L, V)$ that are frames on $U$ and on $V$ respectively, where `IsFrameOn s W` means that for every open $W'$ contained both in the domain of $s$ and in $W$, the map $\Gamma(X, W') \to \Gamma(L, W')$, $g \mapsto g \cdot (s|_{W'})$, is bijective; so $s_U$ freely generates $L$ over $U$ and $s_V$ over $V$. Assume likewise sections $s_U' \in \Gamma(L', U)$, $s_V' \in \Gamma(L', V)$ that are frames on $U$ and on $V$. Finally let $t \in \Gamma(X, U \sqcap V)$ be a section of the structure sheaf on the overlap such that $s_U|_{U \cap V} = t \cdot s_V|_{U \cap V}$ in $\Gamma(L, U \sqcap V)$ and $s_U'|_{U \cap V} = t \cdot s_V'|_{U \cap V}$ in $\Gamma(L', U \sqcap V)$, the restrictions being taken along the inclusions $U \cap V \le U$ and $U \cap V \le V$. The conclusion is that the type of isomorphisms $L \cong L'$ is nonempty, i.e. $L$ and $L'$ are isomorphic as objects of $X.\mathrm{Modules}$.
--
--   This is the two-chart Čech statement that an invertible module trivialised on a two-set open cover is determined up to isomorphism by its transition function, i.e. the injectivity of $\check{H}^1$ of the unit sheaf for a cover by two opens into the Picard group, formulated without choosing a cocycle condition on $X$ itself. It is used for the relative Picard deformation arguments [`AlgebraicGeometry.RelPicard.IsDeformationClassMap.injective`](thm.html#AlgebraicGeometry.RelPicard.IsDeformationClassMap.injective) and [`AlgebraicGeometry.RelPicard.IsDeformationClassMap.surjective`](thm.html#AlgebraicGeometry.RelPicard.IsDeformationClassMap.surjective), and in the analysis of models of modular curves at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_iso_of_map_eq_smul_of_map_eq_smul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_iso_of_map_eq_smul_of_map_eq_smul
    {X : Scheme.{u}} {L L' : X.Modules} {U V : X.Opens} (hUV : U ⊔ V = ⊤)
    {sU : Γ(L, U)} {sV : Γ(L, V)} (hsU : Scheme.Modules.IsFrameOn sU U) (hsV : Scheme.Modules.IsFrameOn sV V)
    {sU' : Γ(L', U)} {sV' : Γ(L', V)} (hsU' : Scheme.Modules.IsFrameOn sU' U) (hsV' : Scheme.Modules.IsFrameOn sV' V)
    (t : Γ(X, U ⊓ V))
    (ht : L.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op sU =
      t • L.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op sV)
    (ht' : L'.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op sU' =
      t • L'.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op sV') :
    Nonempty (L ≅ L') := by sorry
