-- Prove2me | Theorems.Thm_DiazModulus_invisible_two_orbit_space_pole_pencil
-- name    : DiazModulus.invisible_two_orbit_space_pole_pencil
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-01T09:20:29.693052+00:00
-- url     : https://prove2.me/theorems/4a8777ea-f1dc-4b2e-8bbb-70f7a5b4c55e
-- title:
--   In an invisible two-orbit space, an element outside H₀ whose poles lie on the zeros of a quadratic M forces M ∝ P or M ∝ Q, and lies in the matching line
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Put $H_0 = \mathrm{span}(1, u, u^{-1})$. Let $P, Q, S_1, S_2 \in \overline{\mathbb{Q}}[X]$ with $P, Q$ coprime, $\max(\deg P, \deg Q) = 2$ and $\deg S_1, \deg S_2 \leq 2$. Put $g_1 = Q(u)S_1(u)/(uP(u))$, $g_2 = P(u)S_2(u)/(uQ(u))$ and $W_A = \mathrm{span}(1, u, u^{-1}, g_1, g_2)$, the two-orbit shape (D2a) of Theorem NF. Suppose that $P$ and $S_1$ have no common zero on the projective line, and neither have $Q$ and $S_2$: $P, S_1$ are coprime, $Q, S_2$ are coprime, the coefficients of $X^2$ in $P$ and $S_1$ are not both zero, and those in $Q$ and $S_2$ are not both zero. Let $M, R \in \overline{\mathbb{Q}}[X]$ with $M \neq 0$, $\deg M \leq 2$ and $\deg R \leq 4$, and let $f \in W_A$ with $f \notin H_0$ and $f\,uM(u) = R(u)$. Then one of the following holds:
--
--   - $M = kP$ for some $k \in \overline{\mathbb{Q}}$, and $f \in \mathrm{span}(1, u, u^{-1}, g_1)$;
--   - $M = kQ$ for some $k \in \overline{\mathbb{Q}}$, and $f \in \mathrm{span}(1, u, u^{-1}, g_2)$.
--
--   An element $f$ with $f\,uM(u) = R(u)$ and $\deg R \leq 4$ has, beyond the poles allowed in $H_0$, poles only at the zeros of $M$ on the projective line ($M$ read as a binary form of degree $2$). So the only quadratic pole sets met by $W_A$ beyond $H_0$ are the zero sets of $P$ and $Q$, and over each of them $W_A$ has only the line $H_0 + \overline{\mathbb{Q}} g_i$.
--
--   Two polynomials $P, S \in \overline{\mathbb{Q}}[X]$ of degree at most $2$ have a common zero on the projective line if they are not coprime (a common root in $\overline{\mathbb{Q}}$) or their coefficients of $X^2$ are both zero (a common zero at $\infty$, reading $P$ and $S$ as binary forms of degree $2$).
--
--   **Proof.** By `DiazModulus.quadratic_space_mem_iff_numerator`, $f\,uP(u)Q(u) = N(u)$ with $N = PQA + a_1Q^2S_1 + a_2P^2S_2$, so $NM = RPQ$ as $u$ is transcendental. If $a_1 \neq 0$, then $Q^2S_1 \cdot a_1M = P(RQ - QAM - a_2PS_2M)$, and `DiazModulus.binary_quadratic_dvd_of_coprime_mul_eq` at $P$ ($d = 6$, $e = 2$) gives $a_1M = PL_0$ with $L_0$ constant, so $M \in \overline{\mathbb{Q}} P$. Symmetrically, $a_2 \neq 0$ gives $M \in \overline{\mathbb{Q}} Q$. Both cannot hold, as $P, Q$ are coprime with $\max(\deg P, \deg Q) = 2$, and $a_1 = a_2 = 0$ would put $f = A(u)/u$ in $H_0$. So exactly one $a_i$ is non-zero, and $f = A(u)/u + a_ig_i$ lies in $H_0 + \overline{\mathbb{Q}} g_i$.
--
--   **Novelty.** None claimed; routine. A step of the project's proof of Q1.6 (`DiazModulus.invisible_two_orbit_space_configuration_ratio_mobius`): in the language of the project's research notes (R12), the only quadratic pole sets that $W_A$ meets beyond $H_0$ are its two orbits.
-- source:
--   No novelty claimed. A step of the proof of Q1.6 of the Diaz modulus mission's research notes (round R12), for two-orbit spaces. Uses DiazModulus.binary_quadratic_dvd_of_coprime_mul_eq and DiazModulus.quadratic_space_mem_iff_numerator. R21b of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem invisible_two_orbit_space_pole_pencil (u : ℂ) (hu : u ∉ Qbar) (P Q S₁ S₂ : (↥Qbar)[X])
    (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2) (hS₁ : S₁.natDegree ≤ 2) (hS₂ : S₂.natDegree ≤ 2)
    (hPS : IsCoprime P S₁) (hQS : IsCoprime Q S₂)
    (hP2 : P.coeff 2 ≠ 0 ∨ S₁.coeff 2 ≠ 0) (hQ2 : Q.coeff 2 ≠ 0 ∨ S₂.coeff 2 ≠ 0)
    (M R : (↥Qbar)[X]) (hM : M.natDegree ≤ 2) (hM0 : M ≠ 0) (hR : R.natDegree ≤ 4)
    (f : ℂ) (hf : f ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ))
    (hf0 : f ∉ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ)) (hfM : f * (u * aeval u M) = aeval u R) :
    ((∃ k : ↥Qbar, M = C k * P) ∧
        f ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P)} : Set ℂ)) ∨
    ((∃ k : ↥Qbar, M = C k * Q) ∧
        f ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ)) := by
  sorry

end DiazModulus
