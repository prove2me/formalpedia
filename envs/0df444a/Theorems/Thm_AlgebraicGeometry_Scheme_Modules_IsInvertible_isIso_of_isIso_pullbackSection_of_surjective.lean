-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_of_isIso_pullbackSection_of_surjective
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_of_isIso_pullbackSection_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/3d3903db-65ec-574f-b4fc-5eb3746816d3
-- title:
--   Surjective descent of invertibility for a section
-- statement:
--   Let $X$ and $Z$ be schemes (in the bottom universe) and let $g : Z \to X$ be a morphism whose underlying map of topological spaces is surjective. Let $P$ be an object of the category $X.\mathrm{Modules}$ of sheaves of modules on $X$, assumed invertible in the sense of the project's predicate `Scheme.Modules.IsInvertible`: for every point $x \in X$ there is an open $U \subseteq X$ with $x \in U$ such that the pullback of $P$ along the inclusion $U.\iota$ is isomorphic to the unit sheaf of modules on $U$. Let $s : \mathbf{1}_{X.\mathrm{Modules}} \to P$ be a morphism from the monoidal unit, i.e. a global section of $P$, and consider its pullback $\mathrm{pullbackSection}\ g\ s$, the morphism $\mathbf{1}_{Z.\mathrm{Modules}} \to (\mathrm{pullback}\ g).obj\ P$ obtained as the inverse of the canonical isomorphism $\mathrm{pullbackUnitIso}\ g$ followed by $(\mathrm{pullback}\ g).map\ s$. The assertion is: if this pulled-back section is an isomorphism, then $s$ itself is an isomorphism in $X.\mathrm{Modules}$.
--
--   This is the Nakayama-type statement that a global section of an invertible module which becomes a frame after pullback along a morphism hitting every point of the base is already an isomorphism $\mathcal{O}_X \xrightarrow{\sim} P$. It is used in the treatment of polarisations, in the comparison of sections of a line bundle with morphisms to it over a point of the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_of_isIso_pullbackSection_of_surjective.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_of_isIso_pullbackSection_of_surjective
    {X Z : Scheme.{0}} (g : Z ⟶ X) (hg : Function.Surjective g.base)
    (P : X.Modules) (hP : Scheme.Modules.IsInvertible P) (s : 𝟙_ X.Modules ⟶ P)
    (hs : IsIso (Scheme.Modules.pullbackSection g s)) :
    IsIso s := by sorry
