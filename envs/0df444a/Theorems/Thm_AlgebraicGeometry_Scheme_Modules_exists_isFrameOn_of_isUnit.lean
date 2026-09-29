-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_isUnit
-- name    : AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/88ff4f65-2be8-58f7-ac05-44be47a53e6d
-- title:
--   Gluing along a unit: realising a transition function on two opens
-- statement:
--   Let $X$ be a scheme, let $U$ and $V$ be open subsets of $X$, and let $t \in \Gamma(X, U \sqcap V)$ be a section of the structure sheaf over $U \cap V$ which is a unit of that ring. The assertion is that there exist an object $M$ of `X.Modules` (a sheaf of modules over the structure sheaf of $X$) together with sections $a \in \Gamma(M, U)$ and $b \in \Gamma(M, V)$ such that: $a$ is a frame on $U$, meaning that for every open $W \le U$ the map $\Gamma(X, W) \to \Gamma(M, W)$, $g \mapsto g \cdot (a|_W)$, is bijective; $b$ is a frame on $V$ in the same sense, i.e. for every open $W \le V$ the map $g \mapsto g \cdot (b|_W)$ from $\Gamma(X, W)$ to $\Gamma(M, W)$ is bijective; and the two frames are related on the overlap by $b|_{U \cap V} = t \cdot (a|_{U \cap V})$, the restrictions being those of the underlying presheaf of $M$ along the inclusions $U \cap V \le V$ and $U \cap V \le U$. Nothing is asserted about $M$ outside $U \cup V$.
--
--   This is the existence (essential surjectivity) half of the Čech description of modules framed on a two-open cover $\{U, V\}$: every unit on the overlap arises as the transition function between frames, as in the classical gluing of $\mathcal{O}_U$ and $\mathcal{O}_V$ along a $1$-cocycle of units. It is used in the relative Picard deformation argument ([`AlgebraicGeometry.RelPicard.IsDeformationClassMap.surjective`](thm.html#AlgebraicGeometry.RelPicard.IsDeformationClassMap.surjective)) and in the construction of invertible modules on chart models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_isUnit.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_of_isUnit
    {X : Scheme.{u}} (U V : X.Opens) (t : Γ(X, U ⊓ V)) (ht : IsUnit t) :
    ∃ (M : X.Modules) (a : Γ(M, U)) (b : Γ(M, V)),
      Scheme.Modules.IsFrameOn a U ∧ Scheme.Modules.IsFrameOn b V ∧
      M.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op b =
        t • M.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op a := by sorry
