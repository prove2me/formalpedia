-- Prove2me | Theorems.Thm_AddChar_exists_completeOrthogonalIdempotents_forall_mul_eq_pow_mul_of_forall_isUnit_one_sub_pow
-- name    : AddChar.exists_completeOrthogonalIdempotents_forall_mul_eq_pow_mul_of_forall_isUnit_one_sub_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/b508a640-82aa-58f6-aa60-b15e4c29dbd2
-- title:
--   Simultaneous diagonalisation of an additive character by idempotents
-- statement:
--   Let $R$ be a commutative ring, $N$ a natural number such that $N+1$ is a unit in $R$, and $\zeta \in R$ an element with $\zeta^{N+1}=1$ such that $1-\zeta^{j}$ is a unit for every $j$ with $0<j<N+1$. Let $G$ be a finite abelian group in which $(N+1)\cdot g = 0$ for every $g$, and let $\chi$ be an additive character of $G$ with values in $R$, i.e. a map with $\chi(0)=1$ and $\chi(g+g')=\chi(g)\chi(g')$. The assertion is that there exists a family $e$ of elements of $R$, indexed by the finite set of functions $k : G \to \{0,1,\dots,N\}$ (the type `Fin (N+1)`), which is a complete orthogonal family of idempotents in $R$ — each $e_k$ idempotent, $e_k e_{k'} = 0$ for $k \neq k'$, and $\sum_k e_k = 1$ — with the following property: for each index $k$ there is a homomorphism of additive groups $c : G \to \mathbb{Z}/(N+1)$ such that $\chi(g)\,e_k = \zeta^{\,v}\,e_k$ for all $g \in G$, where $v \in \{0,\dots,N\}$ is the canonical representative of $c(g)$.
--
--   After localising at a complete orthogonal family of idempotents, an $R$-valued additive character of a finite abelian group killed by $N+1$ becomes a standard character $g \mapsto \zeta^{c(g)}$ with exponent a homomorphism into $\mathbb{Z}/(N+1)$; note that the exponent homomorphism is only required to work on the corresponding piece, and pieces with $e_k = 0$ impose no condition. The result is used in the treatment of theta structures on polarised abelian schemes, where it supplies the base-change behaviour of frames adapted to a theta group action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddChar_exists_completeOrthogonalIdempotents_forall_mul_eq_pow_mul_of_forall_isUnit_one_sub_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem AddChar.exists_completeOrthogonalIdempotents_forall_mul_eq_pow_mul_of_forall_isUnit_one_sub_pow
    (R : Type u) [CommRing R] (N : ℕ) (hd : IsUnit ((N + 1 : ℕ) : R))
    (ζ : R) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] (hG : ∀ g : G, (N + 1) • g = 0) (χ : AddChar G R) :
    ∃ e : (G → Fin (N + 1)) → R, CompleteOrthogonalIdempotents e ∧
      ∀ k : G → Fin (N + 1), ∃ c : G →+ ZMod (N + 1), ∀ g : G, χ g * e k = ζ ^ (c g).val * e k := by sorry
