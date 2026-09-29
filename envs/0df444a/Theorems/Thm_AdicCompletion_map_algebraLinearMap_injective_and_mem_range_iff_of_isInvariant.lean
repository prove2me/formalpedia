-- Prove2me | Theorems.Thm_AdicCompletion_map_algebraLinearMap_injective_and_mem_range_iff_of_isInvariant
-- name    : AdicCompletion.map_algebraLinearMap_injective_and_mem_range_iff_of_isInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/3dbaec4a-da94-5297-b5cd-ad4e45c8c1ae
-- title:
--   Adic completion of invariants: Noetherian, module-finite case
-- statement:
--   Let $A$ be a commutative Noetherian ring, $I \subseteq A$ an ideal, and let $S$ be a commutative ring that is an $A$-algebra, finite as an $A$-module, and such that $A$ acts faithfully on $S$ (equivalently, the structure map $A \to S$ is injective). Let $G$ be a finite group acting on $S$ by ring automorphisms, the action commuting with the $A$-scalar multiplication, and assume $\mathrm{Algebra.IsInvariant}\ A\ S\ G$: every $s \in S$ fixed by all of $G$ lies in the image of $A$. All completions are $I$-adic completions of $A$-modules, and $\mathrm{AdicCompletion.map}\ I$ is the induced map on completions of an $A$-linear map. The conclusion is a conjunction: first, the map $\widehat{A} \to \widehat{S}$ obtained by completing the $A$-linear structure map $A \to S$ is injective; second, for every $x \in \widehat{S}$, $x$ lies in the range of that map if and only if $x$ is fixed by the completion of each $A$-linear automorphism $s \mapsto g \cdot s$ of $S$, for all $g \in G$. Thus $\widehat{A}$ is identified with the $G$-invariants of $\widehat{S}$ for the completed action.
--
--   This is the statement that forming $I$-adic completions commutes with passage to $G$-invariants, under Noetherian and module-finite hypotheses and with no assumption that $|G|$ be invertible in $A$. It is used by [`Algebra.IsInvariant.isInvariant_adicCompletion_stabilizer_and_injective_and_finite`](thm.html#Algebra.IsInvariant.isInvariant_adicCompletion_stabilizer_and_injective_and_finite), where the group acting may well have order divisible by the residue characteristic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdicCompletion_map_algebraLinearMap_injective_and_mem_range_iff_of_isInvariant.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AdicCompletion.map_algebraLinearMap_injective_and_mem_range_iff_of_isInvariant
    {A : Type*} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {S : Type*} [CommRing S] [Algebra A S] [Module.Finite A S] [FaithfulSMul A S]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G A S]
    [Algebra.IsInvariant A S G] :
    Function.Injective (AdicCompletion.map I (Algebra.linearMap A S)) ∧
    ∀ x : AdicCompletion I S,
      x ∈ LinearMap.range (AdicCompletion.map I (Algebra.linearMap A S)) ↔
        ∀ g : G, AdicCompletion.map I (DistribSMul.toLinearMap A S g) x = x := by sorry
