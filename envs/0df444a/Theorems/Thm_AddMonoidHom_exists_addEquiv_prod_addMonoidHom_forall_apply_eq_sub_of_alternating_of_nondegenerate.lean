-- Prove2me | Theorems.Thm_AddMonoidHom_exists_addEquiv_prod_addMonoidHom_forall_apply_eq_sub_of_alternating_of_nondegenerate
-- name    : AddMonoidHom.exists_addEquiv_prod_addMonoidHom_forall_apply_eq_sub_of_alternating_of_nondegenerate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/96a3bb71-8dfb-52a6-a03f-a0b0a3f5d207
-- title:
--   Symplectic normal form for finite abelian groups with alternating pairing
-- statement:
--   Let $d$ be a natural number that is nonzero, and let $K$ be a finite additive abelian group (a type in `Type`). Let $B : K \to_+ (K \to_+ \mathbb{Z}/d)$ be an additive map into the group of additive maps $K \to \mathbb{Z}/d$, i.e. a biadditive pairing $B : K \times K \to \mathbb{Z}/d$. Assume $B$ is alternating, in the strong sense that $B(a,a) = 0$ for every $a \in K$, and non-degenerate, in the sense that if $a \in K$ satisfies $B(a,b) = 0$ for all $b \in K$ then $a = 0$. The conclusion asserts the existence of a type $L$ together with an additive commutative group structure on it and a `Fintype` structure (so $L$ is a finite abelian group), and of an isomorphism of additive groups $\alpha : L \times (L \to_+ \mathbb{Z}/d) \;\cong\; K$ from the product of $L$ with its group of additive characters valued in $\mathbb{Z}/d$, such that for all $x, x' \in L$ and all additive maps $c, c' : L \to \mathbb{Z}/d$ one has $B\bigl(\alpha(x,c), \alpha(x',c')\bigr) = c(x') - c'(x)$. Thus $\alpha$ transports the standard hyperbolic pairing on $L \times \operatorname{Hom}(L, \mathbb{Z}/d)$ to $B$.
--
--   This is the classification of non-degenerate alternating $\mathbb{Z}/d$-valued pairings on finite abelian groups: every such pairing is isomorphic to the standard symplectic pairing on $L \oplus \operatorname{Hom}(L,\mathbb{Z}/d)$, so in particular $K$ admits a Lagrangian decomposition. It is used via [`ZMod.exists_addEquiv_prod_addMonoidHom_forall_apply_eq_sub_of_alternating_of_nondegenerate`](thm.html#ZMod.exists_addEquiv_prod_addMonoidHom_forall_apply_eq_sub_of_alternating_of_nondegenerate), the version of the same statement for a pairing written with explicit $\mathbb{Z}/d$-coefficients, in the analysis of Weil pairings on torsion of elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddMonoidHom_exists_addEquiv_prod_addMonoidHom_forall_apply_eq_sub_of_alternating_of_nondegenerate.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AddMonoidHom.exists_addEquiv_prod_addMonoidHom_forall_apply_eq_sub_of_alternating_of_nondegenerate
    {d : ℕ} [NeZero d] (K : Type) [AddCommGroup K] [Finite K]
    (B : K →+ K →+ ZMod d) (halt : ∀ a : K, B a a = 0) (hnd : ∀ a : K, (∀ b : K, B a b = 0) → a = 0) :
    ∃ (L : Type) (_ : AddCommGroup L) (_ : Fintype L) (α : L × (L →+ ZMod d) ≃+ K),
      ∀ (x x' : L) (c c' : L →+ ZMod d), B (α (x, c)) (α (x', c')) = c x' - c' x := by sorry
