-- Prove2me | Theorems.Thm_DiazModulus_fischler_linear_pow_prod_mem
-- name    : DiazModulus.fischler_linear_pow_prod_mem
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:16:21.441207+00:00
-- url     : https://prove2.me/theorems/951a2df8-c961-4371-aad6-c61579123182
-- title:
--   If every coefficient of (λ₁X₁ + ⋯ + λₘXₘ)ᵏ lies in ℒ̃, then so does every product λ_I(1) ⋯ λ_I(k) of k coordinates of λ
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $\lambda \in \mathbb C^m$ and $k \ge 0$, and suppose that every coefficient of the polynomial $(\lambda_1 X_1 + \dots + \lambda_m X_m)^k \in \mathbb C[X_1, \dots, X_m]$ lies in $\widetilde{\mathcal L}$. Then
--   $$\lambda_{I(1)} \lambda_{I(2)} \cdots \lambda_{I(k)} \in \widetilde{\mathcal L}$$
--   for every map $I : \{1, \dots, k\} \to \{1, \dots, m\}$.
-- source:
--   Step of the proofs of S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Th. 1.1 and Th. 6.2 (pp. 168–169, 184–185): the coefficients of Λᵏ are positive integer multiples of the products of k coefficients of Λ. Proved by differentiation and induction on k; Fischler also differentiates P (p. 185). Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fischler_linear_pow_prod_mem {m k : ℕ} (Λ : Fin m → ℂ)
    (hP : ∀ s, ((∑ i, MvPolynomial.C (Λ i) * MvPolynomial.X i) ^ k :
      MvPolynomial (Fin m) ℂ).coeff s ∈ LogAlgTilde) :
    ∀ I : Fin k → Fin m, ∏ t, Λ (I t) ∈ LogAlgTilde := by
  sorry

end DiazModulus
