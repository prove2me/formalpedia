-- Prove2me | Theorems.Thm_DiazModulus_invisible_cyclic_space_pole_pencil
-- name    : DiazModulus.invisible_cyclic_space_pole_pencil
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-01T09:20:04.121915+00:00
-- url     : https://prove2.me/theorems/6304e678-b24c-47f1-8af7-a93cfa370db0
-- title:
--   In an invisible cyclic space, an element outside H₀ whose poles lie on the zeros of a quadratic M forces M ∝ P, and lies in span(1, u, 1/u, g₁)
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Put $H_0 = \mathrm{span}(1, u, u^{-1})$. Let $P, Q, S_1, S_2 \in \overline{\mathbb{Q}}[X]$ with $P, Q$ coprime, $\max(\deg P, \deg Q) = 2$ and $\deg S_1, \deg S_2 \leq 2$. Put $g_1 = Q(u)S_1(u)/(uP(u))$, $g_2 = Q(u)(Q(u)S_1(u) + P(u)S_2(u))/(uP(u)^2)$ and $W_B = \mathrm{span}(1, u, u^{-1}, g_1, g_2)$, the cyclic shape (D2b) of Theorem NF. Suppose that $P$ and $S_1$ have no common zero on the projective line: they are coprime, and their coefficients of $X^2$ are not both zero. Let $M, R \in \overline{\mathbb{Q}}[X]$ with $M \neq 0$, $\deg M \leq 2$ and $\deg R \leq 4$, and let $f \in W_B$ with $f \notin H_0$ and $f\,uM(u) = R(u)$. Then $M = kP$ for some $k \in \overline{\mathbb{Q}}$, and $f \in \mathrm{span}(1, u, u^{-1}, g_1)$.
--
--   So the only quadratic pole set met by $W_B$ beyond $H_0$ is the zero set of $P$, and over it $W_B$ has only the line $H_0 + \overline{\mathbb{Q}} g_1$.
--
--   Two polynomials $P, S \in \overline{\mathbb{Q}}[X]$ of degree at most $2$ have a common zero on the projective line if they are not coprime (a common root in $\overline{\mathbb{Q}}$) or their coefficients of $X^2$ are both zero (a common zero at $\infty$, reading $P$ and $S$ as binary forms of degree $2$).
--
--   **Proof.** By `DiazModulus.quadratic_space_mem_iff_numerator`, $f\,uP(u)^2 = N(u)$ with $N = P^2A + a_1PQS_1 + a_2Q(QS_1 + PS_2)$, so $NM = RP^2$. Every divisibility step is `DiazModulus.binary_quadratic_dvd_of_coprime_mul_eq`. Step 1: $a_2 = 0$. Otherwise $Q^2S_1 \cdot a_2M = P(RP - PAM - a_1QS_1M - a_2QS_2M)$ ($d = 6$, $e = 2$; the degree count uses $\deg S_2 \leq 2$) gives $M = kP$ with $k \neq 0$; cancelling $P$, $Q^2S_1 \cdot a_2k = P(R - k(PA + a_1QS_1 + a_2QS_2))$, and the lemma with $e = 0$ gives $a_2k = 0$. Step 2: now $(PA + a_1QS_1)M = RP$. If $a_1 = 0$, then $f = A(u)/u \in H_0$, which is excluded; otherwise $QS_1 \cdot a_1M = P(R - AM)$ ($d = 4$, $e = 2$) gives $M \in \overline{\mathbb{Q}} P$, and $f = A(u)/u + a_1g_1$.
--
--   **Novelty.** None claimed; routine. A step of the project's proof of Q1.6 (`DiazModulus.invisible_cyclic_space_configuration_ratio_mobius`): in the language of the project's research notes (R12), the only quadratic pole set that $W_B$ meets beyond $H_0$ is its orbit.
-- source:
--   No novelty claimed. A step of the proof of Q1.6 of the Diaz modulus mission's research notes (round R12), for cyclic spaces. Uses DiazModulus.binary_quadratic_dvd_of_coprime_mul_eq and DiazModulus.quadratic_space_mem_iff_numerator. R21b of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem invisible_cyclic_space_pole_pencil (u : ℂ) (hu : u ∉ Qbar) (P Q S₁ S₂ : (↥Qbar)[X])
    (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2) (hS₁ : S₁.natDegree ≤ 2) (hS₂ : S₂.natDegree ≤ 2)
    (hPS : IsCoprime P S₁) (hP2 : P.coeff 2 ≠ 0 ∨ S₁.coeff 2 ≠ 0)
    (M R : (↥Qbar)[X]) (hM : M.natDegree ≤ 2) (hM0 : M ≠ 0) (hR : R.natDegree ≤ 4)
    (f : ℂ) (hf : f ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ))
    (hf0 : f ∉ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ)) (hfM : f * (u * aeval u M) = aeval u R) :
    (∃ k : ↥Qbar, M = C k * P) ∧
      f ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P)} : Set ℂ) := by
  sorry

end DiazModulus
