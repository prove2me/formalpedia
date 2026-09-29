-- Prove2me | Theorems.Thm_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
-- name    : AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/5c78d5a9-fd90-5289-b077-4e0b079a4d31
-- title:
--   #A[d]=d² for all d∣ n forces A[n]≅(ℤ/n)²
-- statement:
--   Let $A$ be an additive abelian group, regarded as a $\mathbb Z$-module, and let $n$ be a natural number with $n \neq 0$. For a natural number $d$ write $A[d] = \{x \in A : d \cdot x = 0\}$ for the $d$-torsion submodule `Submodule.torsionBy ℤ A d`. Assume that for every divisor $d$ of $n$ the natural cardinality of $A[d]$ equals $d^2$; since `Nat.card` is $0$ on infinite types and $d \neq 0$ for each divisor of $n$, this hypothesis includes the assertion that each such $A[d]$ is finite, of order exactly $d^2$. The conclusion is that the type of additive group isomorphisms $\mathbb Z/n\mathbb Z \times \mathbb Z/n\mathbb Z \simeq A[n]$ is nonempty, that is, the $n$-torsion subgroup of $A$ is isomorphic, as an abelian group, to the direct square of the cyclic group of order $n$. The statement asserts only the existence of such an isomorphism; no canonical choice of isomorphism or of basis is produced.
--
--   This is the "counting implies structure" step for abelian groups: the hypothesis on the orders of all $A[d]$, $d \mid n$, pins down the isomorphism type of $A[n]$ via the structure theorem for finite abelian groups together with the Chinese remainder decomposition. It is applied to turn cardinality counts of torsion subgroups (for instance $\#E[d] = d^2$ for elliptic curves over an algebraically closed field) into the existence of a torsion basis, and is used in this form by the statements about fake elliptic curves with extra level structure, relative group laws on Jacobians with good reduction, and fibres of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
    {A : Type*} [AddCommGroup A] {n : ℕ} (hn : n ≠ 0)
    (hcard : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ 2) :
    Nonempty (ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n) := by sorry
