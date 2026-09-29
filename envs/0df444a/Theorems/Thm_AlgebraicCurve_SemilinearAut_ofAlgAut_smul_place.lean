-- Prove2me | Theorems.Thm_AlgebraicCurve_SemilinearAut_ofAlgAut_smul_place
-- name    : AlgebraicCurve.SemilinearAut.ofAlgAut_smul_place
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/123af9e6-ffab-5175-857e-aa9cf01ca003
-- title:
--   Compatibility of the two actions of Aut(F/K) on places
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, let $\sigma$ be a $K$-algebra automorphism of $F$, and let $v$ be a place of $F$ over $K$, that is, a valuation subring of $F$ containing the image of $K$, different from all of $F$, and a principal ideal ring. Two group actions on such places are in play. On the one hand, the group `SemilinearAut K F` of those pairs $(\varphi,\tau)$ of ring automorphisms of $F$ and of $K$ satisfying $\varphi(\iota(a)) = \iota(\tau(a))$ for all $a \in K$, $\iota$ the structure map $K \to F$, acts on places; and `ofAlgAut` is the group homomorphism $(F \simeq_{\mathrm{alg}[K]} F) \to$ `SemilinearAut K F` sending $\sigma$ to the pair consisting of $\sigma$ viewed as a ring automorphism of $F$ and the identity of $K$. On the other hand, $K$-algebra automorphisms of $F$ act on places directly. The theorem asserts that these agree: the place $\mathrm{ofAlgAut}(\sigma)\cdot v$ equals the place $\sigma \cdot v$.
--
--   This is the coherence law between the action of $\mathrm{Aut}(F/K)$ on the places of $F/K$ and the action of the larger group of semilinear automorphisms restricted along `ofAlgAut`; both send $v$ to the place whose valuation ring is $\sigma(\mathcal{O}_v)$. It is used to transfer statements about semilinear automorphisms to $K$-algebra automorphisms, for instance in the injectivity results for the divisorial Weil pairing and in the recognition of a semilinear automorphism from its action on the base field and on places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemilinearAut_ofAlgAut_smul_place.lean

import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.SemilinearAut.ofAlgAut_smul_place {K F : Type*} [Field K] [Field F] [Algebra K F] (σ : F ≃ₐ[K] F) (v : Place K F) : ofAlgAut σ • v = σ • v := by sorry
