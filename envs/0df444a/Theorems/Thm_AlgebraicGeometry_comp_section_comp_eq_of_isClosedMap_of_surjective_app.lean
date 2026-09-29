-- Prove2me | Theorems.Thm_AlgebraicGeometry_comp_section_comp_eq_of_isClosedMap_of_surjective_app
-- name    : AlgebraicGeometry.comp_section_comp_eq_of_isClosedMap_of_surjective_app
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/3dbbba04-7240-5099-bf6c-36e606926a7f
-- title:
--   Rigidity over a base with a section and closed projection
-- statement:
--   Let $X$, $B$, $Y$ be schemes (in a fixed universe), let $p \colon X \to B$ be a morphism and let $\varepsilon \colon B \to X$ be a section of $p$, in the sense that the composite of $\varepsilon$ followed by $p$ is the identity of $B$. Assume that the map of underlying topological spaces induced by $p$ is a closed map, and that for every open subset $U \subseteq B$ which is an affine open the ring map $p^{\sharp}_U \colon \Gamma(U, \mathcal{O}_B) \to \Gamma(p^{-1}(U), \mathcal{O}_X)$ on sections is surjective. Let $f \colon X \to Y$ be a morphism of schemes which is constant along the retraction $\varepsilon \circ p$ on points: for every point $x$ of the underlying space of $X$ one has $f(\varepsilon(p(x))) = f(x)$. The conclusion is the equality of morphisms of schemes $p$ followed by $\varepsilon$ followed by $f$ equals $f$, i.e. $f \circ \varepsilon \circ p = f$; so the pointwise factorisation through the image of the section holds already at the level of scheme morphisms.
--
--   This is the rigidity lemma in the form assumed for abelian schemes: the hypothesis $\mathcal{O}_B \to p_*\mathcal{O}_X$ surjective on affine opens (hence an isomorphism, $p$ having a section) replaces the cohomological input "$p$ proper and flat with $H^0$ of the fibres equal to the residue field". It is used in the construction of the group-scheme structure on Jacobians and their good reduction: the commutative-monoid-object statement for a proper flat geometrically integral scheme over a base and the rigidity arguments identifying morphisms of abelian-scheme bundles cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_comp_section_comp_eq_of_isClosedMap_of_surjective_app.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.comp_section_comp_eq_of_isClosedMap_of_surjective_app
    {X B Y : Scheme.{u}} (p : X ⟶ B) (ε : B ⟶ X) (hε : ε ≫ p = 𝟙 B)
    (hp : IsClosedMap p)
    (hH0 : ∀ U : B.Opens, IsAffineOpen U → Function.Surjective (p.app U))
    (f : X ⟶ Y) (hf : ∀ x : X, f (ε (p x)) = f x) :
    p ≫ ε ≫ f = f := by sorry
