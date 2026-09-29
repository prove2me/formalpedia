-- Prove2me | Theorems.Thm_Finite_exists_isUnit_prod_pow_apply_eq_of_isReduced_of_prime
-- name    : Finite.exists_isUnit_prod_pow_apply_eq_of_isReduced_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/3c3c3b08-34d3-5531-b18c-95213f31f350
-- title:
--   Norm surjectivity for prime-order automorphisms of finite reduced rings
-- statement:
--   Let $R$ be a finite reduced commutative ring (commutative ring with the finiteness and reducedness typeclass assumptions), let $\tau \colon R \to R$ be a ring automorphism, i.e. a ring isomorphism of $R$ with itself, and let $\ell$ be a natural number which is prime and satisfies $\tau^{\ell} = 1$ in the automorphism group of $R$. Assume further that $\tau$ acts non-trivially on every stable residue field in the following sense: for every ideal $\mathfrak{m}$ of $R$ which is maximal and satisfies $\tau(x) \in \mathfrak{m}$ for all $x \in \mathfrak{m}$, there exists $x \in R$ with $\tau(x) - x \notin \mathfrak{m}$. Finally let $c \in R$ be a unit fixed by $\tau$, so $\tau(c) = c$. The conclusion is that $c$ lies in the image of the norm attached to $\tau$ on units: there exists $u \in R$ which is a unit and satisfies $$\prod_{i \in \{0,1,\dots,\ell-1\}} (\tau^{i})(u) = c,$$ the product being taken over $i$ in the range $0 \le i < \ell$.
--
--   This is the residual form of the surjectivity of the norm map in an unramified cyclic extension of prime degree, phrased for a finite reduced commutative ring with an automorphism of prime order acting non-trivially on each of its $\tau$-stable residue fields. It is used in the construction of norm strings for integral elements of $\mathrm{GL}_2$ over a local field, namely by [`AutomorphicForm.exists_normString_eq_toTensorGL_of_mem_localIntegralSet_of_ramificationIdx_eq_one_of_prime`](thm.html#AutomorphicForm.exists_normString_eq_toTensorGL_of_mem_localIntegralSet_of_ramificationIdx_eq_one_of_prime), where it supplies the residual step that is then lifted by successive approximation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Finite_exists_isUnit_prod_pow_apply_eq_of_isReduced_of_prime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Finite.exists_isUnit_prod_pow_apply_eq_of_isReduced_of_prime
    {R : Type*} [CommRing R] [Finite R] [IsReduced R]
    (τ : R ≃+* R) (ℓ : ℕ) (hℓ : ℓ.Prime) (hτℓ : τ ^ ℓ = 1)
    (hmax : ∀ m : Ideal R, m.IsMaximal → (∀ x ∈ m, τ x ∈ m) → ∃ x, τ x - x ∉ m)
    (c : R) (hc : IsUnit c) (hτc : τ c = c) :
    ∃ u : R, IsUnit u ∧ ∏ i ∈ Finset.range ℓ, (τ ^ i) u = c := by sorry
