-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
-- name    : AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/667df522-180d-51ad-a913-a2fdf3e58dad
-- title:
--   Isomorphic mathcal O_V-modules have isomorphic ordered Čech cohomology
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme, and $\pi\colon V\to\operatorname{Spec} R$ a morphism of schemes; let $M$ and $M'$ be $\mathcal O_V$-modules (objects of `V.Modules`) together with an isomorphism $e\colon M\cong M'$ in that category, and let $K$ be an ordered affine cover of $V$, that is, a finite linearly ordered index type $\iota$, opens $U_i\subseteq V$ each of which is affine, with $\bigsqcup_i U_i=\top$. Associated with $\pi$ and an $\mathcal O_V$-module is the presheaf datum `OModulePresheaf.ofModules`, which assigns to an open $U$ the sections $\Gamma(M,U)$ with their $\Gamma(V,U)$-module structure and the induced $R$-module structure obtained from $\pi$ via the algebra map $R\to\Gamma(V,U)$, together with the restriction maps of $M$ as $R$-linear maps. For such a datum, $\mathtt{H0}$ denotes the kernel of the differential in degree $0$ of the ordered Čech complex of $K$, and $\mathtt{HSucc}\ i$ the quotient of $\ker d^{i+1}$ by the preimage in it of $\operatorname{range} d^{i}$. The assertion is threefold: there exists an $R$-linear isomorphism between the degree-zero groups of $M$ and $M'$ for $K$; for every $i\in\mathbb N$ there exists an $R$-linear isomorphism between the $i$-th higher groups; and $\mathtt{CechFinite}$, the conjunction that $\mathtt{H0}$ and each $\mathtt{HSucc}\ i$ are finite $R$-modules, holds for $M$ if and only if it holds for $M'$. Only existence of the isomorphisms is asserted (`Nonempty`), no particular one being named.
--
--   This is the invariance of ordered (alternating) Čech cohomology under isomorphism of coefficient $\mathcal O_V$-modules; it is needed because the presheaf datum `OModulePresheaf.ofModules` is a structure assembled by hand rather than the value of a functor. It is used throughout the coherence and Euler-characteristic computations on a two-chart affine cover, for instance to transport vanishing and finiteness statements along an isomorphism with a tensor or pullback module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso.lean

import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) {M M' : V.Modules} (e : M ≅ M')
    (K : V.OrderedAffineCover) :
    Nonempty ((OModulePresheaf.ofModules π M).H0 K ≃ₗ[R] (OModulePresheaf.ofModules π M').H0 K) ∧
      (∀ i : ℕ, Nonempty ((OModulePresheaf.ofModules π M).HSucc K i ≃ₗ[R] (OModulePresheaf.ofModules π M').HSucc K i)) ∧
      ((OModulePresheaf.ofModules π M).CechFinite K ↔ (OModulePresheaf.ofModules π M').CechFinite K) := by sorry
