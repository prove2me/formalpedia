-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_iso_tensorUnit_of_map_eq_mul
-- name    : AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_iso_tensorUnit_of_map_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/022f82f9-293a-5022-ae4a-e6b6db07fa87
-- title:
--   Coboundary transition data trivialises a two-chart framed module
-- statement:
--   Let $X$ be a scheme and $L$ an object of $X$-modules (a presheaf of modules over the structure sheaf). Let $U, V$ be open subsets of $X$ with $U \sqcup V = \top$, i.e. covering $X$. Let $s_U \in \Gamma(L, U)$ and $s_V \in \Gamma(L, V)$ be sections that are frames on their own domains in the following sense: for every open $W \le U$ the map $\Gamma(X, W) \to \Gamma(L, W)$, $g \mapsto g \cdot (s_U|_W)$, is bijective, and likewise for every open $W \le V$ the map $g \mapsto g \cdot (s_V|_W)$ is bijective. Let $t \in \Gamma(X, U \sqcap V)$ be a transition function relating them, $s_U|_{U \cap V} = t \cdot s_V|_{U \cap V}$. Assume finally that $t$ is a coboundary for the given charts: there are sections $a \in \Gamma(X, U)$ and $b \in \Gamma(X, V)$, each a unit in its ring of sections, with $a|_{U \cap V} = t \cdot b|_{U \cap V}$. Then the type of isomorphisms $L \cong \mathbf{1}$ in $X$-modules is nonempty, where $\mathbf{1}$ is the monoidal unit, i.e. $L$ is isomorphic to the structure sheaf; the conclusion asserts existence of such an isomorphism without naming one.
--
--   This is the two-chart case of the Čech description of the Picard group: a line bundle given by frames on the two members of a two-element open cover is trivial exactly when its transition function is a coboundary of units. It is used in the relative Picard and deformation-theoretic parts of the development, for instance in the construction of isomorphisms of twisted pullback modules and in the computation with modules over a scheme extended by dual numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_iso_tensorUnit_of_map_eq_mul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_iso_tensorUnit_of_map_eq_mul
    {X : Scheme.{u}} {L : X.Modules} {U V : X.Opens} (hUV : U ⊔ V = ⊤)
    {sU : Γ(L, U)} {sV : Γ(L, V)} (hsU : Scheme.Modules.IsFrameOn sU U) (hsV : Scheme.Modules.IsFrameOn sV V)
    (t : Γ(X, U ⊓ V))
    (ht : L.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op sU =
      t • L.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op sV)
    (a : Γ(X, U)) (b : Γ(X, V)) (ha : IsUnit a) (hb : IsUnit b)
    (hab : X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op a =
      t * X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op b) :
    Nonempty (L ≅ 𝟙_ X.Modules) := by sorry
