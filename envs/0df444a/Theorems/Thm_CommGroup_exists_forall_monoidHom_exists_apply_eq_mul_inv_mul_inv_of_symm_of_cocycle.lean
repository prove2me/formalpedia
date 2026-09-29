-- Prove2me | Theorems.Thm_CommGroup_exists_forall_monoidHom_exists_apply_eq_mul_inv_mul_inv_of_symm_of_cocycle
-- name    : CommGroup.exists_forall_monoidHom_exists_apply_eq_mul_inv_mul_inv_of_symm_of_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/cb58f1fc-96db-5b73-844a-7bff9c14aed1
-- title:
--   Symmetric cocycles on a finite abelian group split after adjoining roots
-- statement:
--   Let $K$ be a finite additive abelian group, let $A$ be a multiplicative abelian group, and let $c : K \times K \to A$ be a function which is symmetric, $c(k,k') = c(k',k)$ for all $k,k'$, and satisfies the $2$-cocycle identity $c(k,k')\,c(k+k',k'') = c(k',k'')\,c(k,k'+k'')$ for all $k,k',k''$. The assertion is that there exist a natural number $m$, a family $a : \mathrm{Fin}\,m \to A$ and a family of natural numbers $n : \mathrm{Fin}\,m \to \mathbb{N}$ such that, first, each $n_i$ is strictly positive and divides the cardinality of $K$, and, second, for every abelian group $A'$ (in the same universe as $A$) and every group homomorphism $\varphi : A \to A'$ with the property that each $\varphi(a_i)$ admits an $n_i$-th root in $A'$, that is, $\alpha^{n_i} = \varphi(a_i)$ for some $\alpha \in A'$, there is a function $b : K \to A'$ with $\varphi(c(k,k')) = b(k+k')\,b(k)^{-1}\,b(k')^{-1}$ for all $k,k' \in K$. Thus the push-forward of $c$ along $\varphi$ is a coboundary, and the finitely many obstruction elements $a_i$, together with their exponents $n_i$, are produced once and for all from $c$, independently of $\varphi$ and $A'$.
--
--   A symmetric $2$-cocycle on a finite abelian group classifies a commutative central extension of $K$ by $A$, and a function $b$ as in the conclusion is precisely a splitting homomorphism of that extension; the statement isolates a finite list of elements of $A$ whose roots suffice to produce such a splitting. It is used by [`CommRing.exists_etale_faithfullyFlat_units_eq_mul_inv_mul_inv_of_symm_of_cocycle_of_isUnit_card`](thm.html#CommRing.exists_etale_faithfullyFlat_units_eq_mul_inv_mul_inv_of_symm_of_cocycle_of_isUnit_card), where the roots are obtained after an étale faithfully flat base change of the coefficient ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CommGroup_exists_forall_monoidHom_exists_apply_eq_mul_inv_mul_inv_of_symm_of_cocycle.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem CommGroup.exists_forall_monoidHom_exists_apply_eq_mul_inv_mul_inv_of_symm_of_cocycle
    {K : Type u} [AddCommGroup K] [Finite K] {A : Type v} [CommGroup A] (c : K → K → A)
    (hsymm : ∀ k k', c k k' = c k' k) (hcoc : ∀ k k' k'', c k k' * c (k + k') k'' = c k' k'' * c k (k' + k'')) :
    ∃ (m : ℕ) (a : Fin m → A) (n : Fin m → ℕ), (∀ i, 0 < n i ∧ n i ∣ Nat.card K) ∧
      ∀ (A' : Type v) [CommGroup A'] (φ : A →* A'), (∀ i, ∃ α : A', α ^ (n i) = φ (a i)) →
        ∃ b : K → A', ∀ k k', φ (c k k') = b (k + k') * (b k)⁻¹ * (b k')⁻¹ := by sorry
