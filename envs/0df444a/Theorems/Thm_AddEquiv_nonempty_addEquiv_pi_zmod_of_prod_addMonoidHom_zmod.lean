-- Prove2me | Theorems.Thm_AddEquiv_nonempty_addEquiv_pi_zmod_of_prod_addMonoidHom_zmod
-- name    : AddEquiv.nonempty_addEquiv_pi_zmod_of_prod_addMonoidHom_zmod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/961a0662-6e16-511b-8979-344787b93780
-- title:
--   Cancellation: LtimesHom(L,ℤ/d)≅ H× H forces L≅ H
-- statement:
--   Let $g$ and $d$ be natural numbers and let $\delta \colon \mathrm{Fin}\,g \to \mathbb N$ be a family of nonzero natural numbers with $\prod_{i} \delta_i = d$; write $H = \prod_{i \in \mathrm{Fin}\,g} \mathbb Z/\delta_i$ for the associated product of cyclic groups. Let $L$ be a finite abelian group (a type in `Type` with an additive commutative group structure and finiteness), and suppose given an isomorphism of additive groups $$L \times (L \to_{+} \mathbb Z/d) \;\cong\; H \times H,$$ where $L \to_{+} \mathbb Z/d$ denotes the group of additive homomorphisms from $L$ to $\mathbb Z/d$ with pointwise addition. The conclusion is that the type of additive group isomorphisms $L \cong H$ is nonempty, i.e. $L$ is isomorphic to $\prod_i \mathbb Z/\delta_i$. The assertion is the existence statement `Nonempty (L ≃+ …)` rather than a designated isomorphism; no compatibility between the given isomorphism and the asserted one is claimed.
--
--   A cancellation statement for finite abelian groups, resting on the fact that such a group is determined up to isomorphism by the orders of its $N$-torsion subgroups for all $N$. It is used in the construction of a symplectic-type standard form, namely by [`ZMod.exists_addEquiv_prod_addMonoidHom_forall_apply_eq_sub_of_alternating_of_nondegenerate`](thm.html#ZMod.exists_addEquiv_prod_addMonoidHom_forall_apply_eq_sub_of_alternating_of_nondegenerate), where a finite abelian group carrying a nondegenerate alternating pairing is put into the shape $\prod_i \mathbb Z/\delta_i$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddEquiv_nonempty_addEquiv_pi_zmod_of_prod_addMonoidHom_zmod.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators

theorem AddEquiv.nonempty_addEquiv_pi_zmod_of_prod_addMonoidHom_zmod
    {g d : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = d)
    (L : Type) [AddCommGroup L] [Finite L]
    (e : L × (L →+ ZMod d) ≃+ (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))) :
    Nonempty (L ≃+ ((i : Fin g) → ZMod (δ i))) := by sorry
