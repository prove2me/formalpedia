-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff
-- name    : AlgebraicGeometry.OModulePresheaf.cechFinite_pushforward_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/87a5f1a2-d91f-5be3-8c6a-260c3b24a9cb
-- title:
--   Čech finiteness is preserved by pushforward along a closed immersion
-- statement:
--   Let $R$ be a commutative ring, let $V$ and $Z$ be schemes, let $\pi\colon V\to\operatorname{Spec}R$ be a morphism and let $i\colon Z\to V$ be a closed immersion. Let $H$ be an `OModulePresheaf` for the composite $i$ followed by $\pi$, that is: an assignment of an $R$-module $H(W)$ to each open $W\subseteq Z$, together with a $\Gamma(Z,W)$-module structure on $H(W)$ compatible with the $R$-structure through the algebra map induced by $i \gg \pi$, and $R$-linear restriction maps for $W\le W'$ which are semilinear over restriction of sections and satisfy the identity and composition laws. Let $K$ be a finite ordered affine open cover of $V$: a finite linearly ordered index set together with affine opens $U_j\subseteq V$ whose supremum is $\top$. Then the pushforward presheaf $U\mapsto H(i^{-1}U)$ on $V$, with its $\Gamma(V,U)$-action through $i^{\#}$, has all Čech cohomology modules (the zeroth one and each $\ker d^{q+1}/\operatorname{im}d^{q}$) finite over $R$ for the cover $K$ if and only if $H$ has all Čech cohomology modules finite over $R$ for the cover $(i^{-1}U_j)_j$ of $Z$.
--
--   This is the formal counterpart of the standard reduction of finiteness of coherent cohomology on a closed subscheme to the ambient scheme, Čech cohomology of $i_*\mathcal H$ on $V$ agreeing with that of $\mathcal H$ on $Z$. It is used in the proofs of [`AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper) and [`AlgebraicGeometry.OModulePresheaf.cechFinite_preimage_of_ih`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_preimage_of_ih), where finiteness is propagated from a closed subscheme to its ambient scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff.lean

import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Finiteness.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.cechFinite_pushforward_iff
    {R : Type u} [CommRing R] {V Z : Scheme.{u}} {π : V ⟶ Spec (.of R)} (i : Z ⟶ V) [IsClosedImmersion i]
    (H : OModulePresheaf (i ≫ π)) (K : V.OrderedAffineCover) :
    (OModulePresheaf.pushforward π i H).CechFinite K ↔ H.CechFinite (K.preimage i) := by sorry
