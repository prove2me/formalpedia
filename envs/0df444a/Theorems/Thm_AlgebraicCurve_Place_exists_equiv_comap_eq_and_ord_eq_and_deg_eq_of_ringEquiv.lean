-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_equiv_comap_eq_and_ord_eq_and_deg_eq_of_ringEquiv
-- name    : AlgebraicCurve.Place.exists_equiv_comap_eq_and_ord_eq_and_deg_eq_of_ringEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/fe64c58b-19c9-5cd1-86f4-758a9cee0de6
-- title:
--   Transport of places along compatible isomorphisms K≃ K', F≃ F'
-- statement:
--   Let $K,K',F,F'$ be fields with $F$ a $K$-algebra and $F'$ a $K'$-algebra, let $e : K \simeq K'$ and $\varphi : F \simeq F'$ be ring isomorphisms, and assume the compatibility $\varphi(\iota_K(a)) = \iota_{K'}(e(a))$ for all $a \in K$, where $\iota_K, \iota_{K'}$ denote the structure maps. Here a place of $F$ over $K$ is a valuation subring $\mathcal{O}_v \subseteq F$ containing $\iota_K(K)$, different from $F$ itself, and whose underlying ring is a principal ideal ring. The assertion is that there exists a bijection $\Phi$ between the places of $F$ over $K$ and the places of $F'$ over $K'$ such that, for every place $v$ of $F$ over $K$: first, the valuation subring of $\Phi v$ is the preimage of $\mathcal{O}_v$ under $\varphi^{-1}$, that is $\varphi(\mathcal{O}_v)$; second, $\operatorname{ord}_{\Phi v}(\varphi f) = \operatorname{ord}_v(f)$ for every $f \in F$, where $\operatorname{ord}$ is minus the logarithm of the adic valuation attached to the height-one prime of the valuation ring; and third, $\deg(\Phi v) = \deg(v)$, the degrees being the $K'$- and $K$-dimensions of the respective residue fields. Only a bijection of types is produced, with these three compatibilities.
--
--   This is the standard transport of places of a function field along an isomorphism of function fields lying over an isomorphism of the constant fields; for $K = K'$, $F = F'$ and $e = \mathrm{id}$ it specialises to the action of $\operatorname{Aut}(F/K)$ on places. It is used in the transport of divisor classes, namely by [`AlgebraicCurve.Pic0.exists_equiv_addEquiv_mk_eq_and_smul_of_ringEquiv`](thm.html#AlgebraicCurve.Pic0.exists_equiv_addEquiv_mk_eq_and_smul_of_ringEquiv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_equiv_comap_eq_and_ord_eq_and_deg_eq_of_ringEquiv.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_JZeroTateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_equiv_comap_eq_and_ord_eq_and_deg_eq_of_ringEquiv
    {K K' F F' : Type} [Field K] [Field K'] [Field F] [Field F'] [Algebra K F] [Algebra K' F']
    (e : K ≃+* K') (φ : F ≃+* F') (hφ : ∀ a : K, φ (algebraMap K F a) = algebraMap K' F' (e a)) :
    ∃ Φ : Place K F ≃ Place K' F',
      (∀ v : Place K F, (Φ v).toValuationSubring = v.toValuationSubring.comap φ.symm.toRingHom) ∧
      (∀ (v : Place K F) (f : F), (Φ v).ord (φ f) = v.ord f) ∧
      (∀ v : Place K F, (Φ v).deg = v.deg) := by sorry
