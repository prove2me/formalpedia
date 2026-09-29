-- Prove2me | Theorems.Thm_AlgHom_ker_mem_minimalPrimes_of_transcendental_of_isIntegral_adjoin_singleton
-- name    : AlgHom.ker_mem_minimalPrimes_of_transcendental_of_isIntegral_adjoin_singleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/aa234d0a-ed89-5657-a616-b563064ce317
-- title:
--   Kernel of a transcendental A₀-algebra map is a minimal prime
-- statement:
--   Let $A_0$ and $R$ be commutative rings and $K$ a field, with $R$ and $K$ both $A_0$-algebras, let $j_0 \in R$, and let $\iota : R \to K$ be an $A_0$-algebra homomorphism. Assume two things: first, that $\iota(j_0)$ is transcendental over $A_0$, i.e. the only polynomial $f \in A_0[X]$ with $f(\iota(j_0)) = 0$ (evaluated through the structure map $A_0 \to K$) is $f = 0$; second, that $R$ is integral over the $A_0$-subalgebra $A_0[j_0] = \mathrm{adjoin}_{A_0}\{j_0\}$ of $R$, that is, every element of $R$ satisfies a monic polynomial with coefficients in that subalgebra. The conclusion is that the kernel of the underlying ring homomorphism of $\iota$ belongs to the minimal primes over the zero ideal of $R$: $\ker \iota$ is a prime ideal containing $\bot$, and any prime ideal $\mathfrak q$ of $R$ with $\mathfrak q \subseteq \ker \iota$ satisfies $\ker \iota \subseteq \mathfrak q$. In other words, $\ker \iota$ is a minimal prime of $R$.
--
--   An elementary piece of commutative algebra: transcendence of the image of a single generator, together with integrality of $R$ over the subalgebra it generates, pins the kernel of a map to a field down to a minimal prime. It is applied in the study of the classification maps on modular curves, where it identifies the kernel of a specialisation homomorphism as a minimal prime of the ambient ring from transcendence of the image of a $j$-invariant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgHom_ker_mem_minimalPrimes_of_transcendental_of_isIntegral_adjoin_singleton.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgHom.ker_mem_minimalPrimes_of_transcendental_of_isIntegral_adjoin_singleton
    (A₀ R K : Type) [CommRing A₀] [CommRing R] [Field K] [Algebra A₀ R] [Algebra A₀ K]
    (j₀ : R) (ι : R →ₐ[A₀] K) (htr : Transcendental A₀ (ι j₀))
    (hint : Algebra.IsIntegral ↥(Algebra.adjoin A₀ {j₀}) R) :
    RingHom.ker ι.toRingHom ∈ (⊥ : Ideal R).minimalPrimes := by sorry
