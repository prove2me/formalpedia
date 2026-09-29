-- Prove2me | Theorems.Thm_AlgebraicGeometry_eq_of_comp_eq_of_formallyUnramified_of_preconnectedSpace
-- name    : AlgebraicGeometry.eq_of_comp_eq_of_formallyUnramified_of_preconnectedSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/91bb8fa5-fd3e-5f00-9faa-36655dfcdf0b
-- title:
--   Rigidity of unramified separated morphisms over a connected base
-- statement:
--   Let $X$, $Y$, $T$, $Z$ be schemes and let $g \colon X \to Y$ be a morphism of schemes which is formally unramified, locally of finite type and separated (these three properties being Mathlib's predicates `FormallyUnramified`, `LocallyOfFiniteType` and `IsSeparated` for $g$), and suppose the underlying topological space of $T$ is preconnected. Let $u_1, u_2 \colon T \to X$ be two morphisms with $u_1$ followed by $g$ equal to $u_2$ followed by $g$, i.e. $g \circ u_1 = g \circ u_2$, so that $u_1$ and $u_2$ are morphisms of $Y$-schemes. Assume further that there is a morphism $p \colon Z \to T$ with $Z$ having nonempty underlying space such that $p$ followed by $u_1$ equals $p$ followed by $u_2$, that is $u_1 \circ p = u_2 \circ p$. The conclusion is that $u_1 = u_2$ as morphisms $T \to X$. Note that $T$ is only assumed preconnected rather than connected; nonemptiness of $T$ is supplied instead by the nonempty scheme $Z$ mapping to it.
--
--   This is the classical rigidity statement for unramified separated morphisms: a $Y$-morphism from a connected scheme to an unramified separated $Y$-scheme is determined by its restriction along any morphism from a nonempty scheme, in particular by its value at a single point (SGA 1, Exposé I, Corollaire 5.4; EGA IV, 17.4.9). It is used in the treatment of the relative group law on elliptic curves, for the uniqueness of morphisms agreeing on a torsion point, and in the construction of extensions of homomorphisms to Picard groups of Néron models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_eq_of_comp_eq_of_formallyUnramified_of_preconnectedSpace.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.eq_of_comp_eq_of_formallyUnramified_of_preconnectedSpace
    {X Y T Z : Scheme.{u}} (g : X ⟶ Y) [FormallyUnramified g] [LocallyOfFiniteType g]
    [IsSeparated g] [PreconnectedSpace T]
    (u₁ u₂ : T ⟶ X) (hg : u₁ ≫ g = u₂ ≫ g)
    (p : Z ⟶ T) [Nonempty Z] (hp : p ≫ u₁ = p ≫ u₂) :
    u₁ = u₂ := by sorry
