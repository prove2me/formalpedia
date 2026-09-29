-- Prove2me | Theorems.Thm_CohCarrier_transfer_restrict_eq_pow_index
-- name    : CohCarrier.transfer_restrict_eq_pow_index
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/b0941c4b-9d0f-523f-bbd7-5b769f143221
-- title:
--   Transfer of a restricted character is the [G:K]-th power
-- statement:
--   Let $G$ be a group, $K \le G$ a subgroup of finite index (the Mathlib typeclass `Subgroup.FiniteIndex`), $C$ a commutative group, and $\varphi : G \to C$ a group homomorphism. Write $\varphi|_K$ for the restriction `φ.domRestrict K`, a homomorphism $K \to C$. The assertion is an equality of homomorphisms $G \to C$: the transfer (Verlagerung) `MonoidHom.transfer` of $\varphi|_K$ along the inclusion $K \le G$ — defined in Mathlib, for $C$ abelian and $[G:K]$ finite, by the usual coset-product formula, independently of the chosen left transversal — coincides with the $[G:K]$-th power $\varphi^{[G:K]}$ in the group of homomorphisms $G \to C$, i.e. $\mathrm{tr}(\varphi|_K)(g) = \varphi(g)^{[G:K]}$ for every $g \in G$, where $[G:K]$ is `Subgroup.index`. Note that no hypothesis of finiteness on $G$ or $C$ is imposed, only finiteness of the index, and that the target is required to be commutative so that the transfer is defined.
--
--   This is the degree-one, trivial-coefficients case of the identity $\mathrm{cor} \circ \mathrm{res} = [G:K]$ for group cohomology, the transfer in $H^1(G,C) = \mathrm{Hom}(G,C)$ being corestriction. It is used in the project when comparing characters of a group with characters of a finite-index subgroup, notably in the treatment of Hecke operators and of maximal ideals attached to absolutely irreducible representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_transfer_restrict_eq_pow_index.lean

import Mathlib.GroupTheory.Transfer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.transfer_restrict_eq_pow_index {G : Type*} [Group G] (K : Subgroup G) [K.FiniteIndex] {C : Type*} [CommGroup C]
    (φ : G →* C) :
    MonoidHom.transfer (φ.domRestrict K) = φ ^ K.index := by sorry
