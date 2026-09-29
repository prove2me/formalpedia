-- Prove2me | Theorems.Thm_AddCommGroup_nonempty_addMonoidHom_zmod_addEquiv_of_forall_nsmul_eq_zero
-- name    : AddCommGroup.nonempty_addMonoidHom_zmod_addEquiv_of_forall_nsmul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/76541405-961a-54e2-a5a5-1c5efb9e0206
-- title:
--   A finite abelian group killed by d is isomorphic to Hom(L,ℤ/d)
-- statement:
--   Let $L$ be a finite additive abelian group (in a fixed universe), and let $d$ be a natural number which is nonzero, subject to the hypothesis that $d \cdot x = 0$ for every $x \in L$, i.e. $d$ annihilates $L$. The conclusion asserts that the type of additive group isomorphisms between the group $L \to_+ \mathbb{Z}/d$ of additive homomorphisms from $L$ to $\mathbb{Z}/d$ (with pointwise addition) and $L$ itself is nonempty; that is, $\operatorname{Hom}(L,\mathbb{Z}/d) \cong L$ as abelian groups. Only the existence of such an isomorphism is asserted: no particular isomorphism is produced, and in particular no canonicity or naturality in $L$ is claimed, which is the appropriate form since the isomorphism depends on a choice of decomposition of $L$ into cyclic factors.
--
--   This is the standard statement that the group of $\mathbb{Z}/d$-valued characters of a finite abelian group killed by $d$ is (non-canonically) isomorphic to the group itself, the additive counterpart of the duality for finite abelian groups. It is used by [`AddEquiv.nonempty_addEquiv_pi_zmod_of_prod_addMonoidHom_zmod`](thm.html#AddEquiv.nonempty_addEquiv_pi_zmod_of_prod_addMonoidHom_zmod), in the bookkeeping of finite abelian groups arising as Selmer-type or congruence modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddCommGroup_nonempty_addMonoidHom_zmod_addEquiv_of_forall_nsmul_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem AddCommGroup.nonempty_addMonoidHom_zmod_addEquiv_of_forall_nsmul_eq_zero
    (L : Type u) [AddCommGroup L] [Finite L] (d : ℕ) [NeZero d] (hd : ∀ x : L, d • x = 0) :
    Nonempty ((L →+ ZMod d) ≃+ L) := by sorry
