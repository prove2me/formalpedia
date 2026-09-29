-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_comp_eq
-- name    : AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/88d00420-9952-5ee5-979e-4a82f52f68ae
-- title:
--   Fibrewise h⁰ is invariant under field extension
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a proper morphism. Let $M$ be a sheaf of modules on $A$ which is invertible in the sense of the predicate `Scheme.Modules.IsInvertible`: every point of $A$ has an open neighbourhood $U$ such that the pullback of $M$ along the open immersion $U \hookrightarrow A$ is isomorphic to the unit sheaf of modules on $U$. Let $k$ and $K$ be fields, $sk : S \to k$ a ring homomorphism and $j : k \to K$ a ring homomorphism. The assertion is the equality of the two natural numbers $\mathtt{geomFibreH0Finrank}$ attached to the composite $j \circ sk$ and to $sk$; by definition, $\mathtt{geomFibreH0Finrank}\ f\ M\ k\ sk$ is the $k$-dimension (`Module.finrank`, hence $0$ by convention in the infinite-dimensional case) of the space of global sections of the pullback of $M$ to the fibre product $A \times_{\operatorname{Spec} S} \operatorname{Spec} k$, regarded as a $k$-vector space through the structure morphism to $\operatorname{Spec} k$. Thus $\dim_K \Gamma(A \times_S \operatorname{Spec} K, M_K) = \dim_k \Gamma(A \times_S \operatorname{Spec} k, M_k)$ for any extension $j : k \to K$.
--
--   This is the invariance of $h^0$ of a line bundle on a proper fibre under extension of the base field, a form of flat base change for global sections. It is used in the treatment of polarisations, where the degree condition $h^0 = d$ on geometric fibres has to be checked after passing to a larger field, and is cited by the results on positivity of $\mathtt{geomFibreH0Finrank}$ for polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_comp_eq
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) [IsProper f]
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (k K : Type u) [Field k] [Field K] (sk : S →+* k) (j : k →+* K) :
    Scheme.Modules.geomFibreH0Finrank f M K (j.comp sk) = Scheme.Modules.geomFibreH0Finrank f M k sk := by sorry
