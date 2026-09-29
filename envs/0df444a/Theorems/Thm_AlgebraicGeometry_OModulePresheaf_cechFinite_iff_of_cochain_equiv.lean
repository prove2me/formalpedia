-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_iff_of_cochain_equiv
-- name    : AlgebraicGeometry.OModulePresheaf.cechFinite_iff_of_cochain_equiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/d0126a3e-426f-5517-9064-fd7a16fa6782
-- title:
--   Čech finiteness transfers along an isomorphism of cochain complexes
-- statement:
--   Let $R$ be a commutative ring, let $V$ and $V'$ be schemes with morphisms $\pi : V \to \operatorname{Spec} R$ and $\pi' : V' \to \operatorname{Spec} R$, and let $F$ and $G$ be `OModulePresheaf` data over $\pi$ and $\pi'$ respectively, that is, an assignment of an $R$-module and $\Gamma(V,U)$-module structure (compatible via the scalar tower coming from the algebra structure on $\Gamma(V,U)$ induced by the morphism to $\operatorname{Spec} R$) to each open $U$, together with $R$-linear restriction maps that are semilinear for restriction of sections and satisfy the usual reflexivity and composition identities. Let $K$ and $K'$ be ordered affine covers of $V$ and $V'$, each consisting of a finite linearly ordered index type and affine opens whose supremum is $\top$; for $q \in \mathbb{N}$ the cochain module `F.cochain K q` is the product of $F.\mathrm{obj}$ over the intersections $\bigsqcap_j K.U(s_j)$ indexed by $s \in K.\mathrm{Idx}\, q$, with differentials `F.d K q`. Assume given $R$-linear isomorphisms $e_q :$ `F.cochain K q` $\to$ `G.cochain K' q` for every $q$ satisfying $e_{q+1}(F.d\,K\,q\,x) = G.d\,K'\,q\,(e_q x)$ for all $q$ and all $x$. Then `F.CechFinite K` holds if and only if `G.CechFinite K'` does, where `CechFinite` asserts that the module `H0` of the complex is finite over $R$ and that for every $i$ the module $\ker(d^{\,i+1})/\,(\operatorname{range} d^{\,i}$ pulled back along the inclusion of $\ker(d^{\,i+1}))$ is finite over $R$.
--
--   This is the invariance of finiteness of Čech cohomology under an isomorphism of Čech cochain complexes, in the explicit cocycle-modulo-coboundary form used throughout the treatment of ordered affine covers. It is cited by [`AlgebraicGeometry.OModulePresheaf.cechFinite_pushforward_iff`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_pushforward_iff), where it transfers Čech finiteness between a scheme and its image under a push-forward.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_iff_of_cochain_equiv.lean

import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.RingTheory.Finiteness.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.cechFinite_iff_of_cochain_equiv
    {R : Type u} [CommRing R] {V V' : Scheme.{u}} {π : V ⟶ Spec (.of R)} {π' : V' ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (G : OModulePresheaf π') (K : V.OrderedAffineCover) (K' : V'.OrderedAffineCover)
    (e : ∀ q, F.cochain K q ≃ₗ[R] G.cochain K' q) (he : ∀ q x, e (q + 1) (F.d K q x) = G.d K' q (e q x)) :
    F.CechFinite K ↔ G.CechFinite K' := by sorry
