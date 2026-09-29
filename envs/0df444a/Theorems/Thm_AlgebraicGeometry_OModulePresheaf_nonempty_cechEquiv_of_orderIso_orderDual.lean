-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual
-- name    : AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_of_orderIso_orderDual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/4ff01db4-ab76-59ac-be08-f73d5b516f7f
-- title:
--   Invariance of Čech cohomology under order-reversing re-indexing
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme, $\pi\colon V \to \operatorname{Spec} R$ a morphism, and let $F$ be an `OModulePresheaf` for $\pi$: a family of abelian groups $F(U)$ indexed by the opens $U$ of $V$, each carrying an $R$-module structure and a $\Gamma(V,U)$-module structure compatible via the $R$-algebra structure on $\Gamma(V,U)$ induced by $\pi$, together with $R$-linear restriction maps $F(U') \to F(U)$ for $U \le U'$ that are semilinear for the restriction of sections, reduce to the identity for $U = U'$ and compose functorially; no sheaf or quasi-coherence condition is imposed. Let $K$ and $K'$ be two ordered affine covers of $V$, i.e. each consists of a finite linearly ordered index type together with affine opens indexed by it whose supremum is $\top$. Assume given an order isomorphism $e$ from the index type of $K$ onto the order dual of that of $K'$, so an order-reversing bijection, such that $K'.U(e(i)) = K.U(i)$ for every index $i$ of $K$, the charts being literally the same opens. The conclusion asserts that the $R$-module $F.H0\,K$ is isomorphic, as an $R$-module, to $F.H0\,K'$, and that for every natural number $i$ the quotient of $\ker(F.d\,K\,(i+1))$ by the preimage in it of $\operatorname{range}(F.d\,K\,i)$ is isomorphic, as an $R$-module, to the corresponding quotient formed from $K'$; both assertions are stated as nonemptiness of the respective types of $R$-linear equivalences, so no specific isomorphism is named.
--
--   This is the invariance of alternating Čech cohomology under re-indexing a cover by an order-reversing bijection of index sets leaving the charts unchanged; it complements the order-preserving re-indexing statement and shows that the alternating Čech modules of such a datum depend on the cover only through the family of opens. It is used in the comparison of Čech cohomology for a presheaf-of-modules datum attached to a quasi-coherent module over a separated scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_of_orderIso_orderDual
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F : OModulePresheaf π)
    (K K' : V.OrderedAffineCover) (e : K.ι ≃o (K'.ι)ᵒᵈ) (hU : ∀ i, K'.U (OrderDual.ofDual (e i)) = K.U i) :
    Nonempty (F.H0 K ≃ₗ[R] F.H0 K') ∧ ∀ i : ℕ, Nonempty (F.HSucc K i ≃ₗ[R] F.HSucc K' i) := by sorry
