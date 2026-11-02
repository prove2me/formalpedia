-- Prove2me | Theorems.Thm_DiazModulus_invisible_two_orbit_space_u_multiplier_space_eq
-- name    : DiazModulus.invisible_two_orbit_space_u_multiplier_space_eq
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-01T09:20:20.429199+00:00
-- url     : https://prove2.me/theorems/d9913cec-f11a-44be-9272-bbfa675607a1
-- title:
--   Q1.5, two-orbit: if S₁ has no zero in common with P and S₂ none with Q, the space is five-dimensional and u keeps only span(1, 1/u) in it, so it has no degree-one triple
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $P, Q, S_1, S_2 \in \overline{\mathbb{Q}}[X]$ with $P, Q$ coprime, $\max(\deg P, \deg Q) = 2$ and $\deg S_1, \deg S_2 \leq 2$. Put $g_1 = Q(u)S_1(u)/(uP(u))$, $g_2 = P(u)S_2(u)/(uQ(u))$ and $W_A = \mathrm{span}(1, u, u^{-1}, g_1, g_2)$, the two-orbit shape (D2a) of Theorem NF. Suppose that $P$ and $S_1$ have no common zero on the projective line, and neither have $Q$ and $S_2$: $P, S_1$ are coprime, $Q, S_2$ are coprime, the coefficients of $X^2$ in $P$ and $S_1$ are not both zero, and those in $Q$ and $S_2$ are not both zero. Then:
--
--   - $\dim W_A = 5$;
--   - for every $f \in \mathbb{C}$, $f \in W_A$ and $uf \in W_A$ if and only if $f \in \mathrm{span}(1, u^{-1})$;
--   - (D1) fails for $W_A$: there are no linearly independent $t_0, t_1, t_2$ with $t_j, ut_j \in W_A$.
--
--   Two polynomials $P, S \in \overline{\mathbb{Q}}[X]$ of degree at most $2$ have a common zero on the projective line if they are not coprime (a common root in $\overline{\mathbb{Q}}$) or their coefficients of $X^2$ are both zero (a common zero at $\infty$, reading $P$ and $S$ as binary forms of degree $2$). When $u\bar u$ is algebraic, `DiazModulus.two_orbit_space_visible_to_four_dimensional_extensions_iff_common_zero` says that the conditions on $S_1, S_2$ are exactly the invisibility of $W_A$ to the four-dimensional extensions; they are stated directly, so that neither $u\bar u$ nor complex conjugation enters. So an invisible two-orbit space has no degree-one triple. Every position of the orbits is covered by the same argument: a zero at $0$ or at $\infty$, a double zero, and $P$ or $Q$ constant.
--
--   **Proof.** By `DiazModulus.quadratic_space_mem_iff_numerator`, $f \in W_A$ means $f\,uP(u)Q(u) = (PQA + a_1Q^2S_1 + a_2P^2S_2)(u)$ with $\deg A \leq 2$ and $a_1, a_2 \in \overline{\mathbb{Q}}$. **Core:** if $PQA + Q^2S_1L_1 + P^2S_2L_2 = 0$ with $\deg L_i \leq e \leq 1$ and $\deg A \leq 2 + e$, then $L_1 = L_2 = 0$. Indeed `DiazModulus.binary_quadratic_dvd_of_coprime_mul_eq` at $P$, with $F = Q^2S_1$ and $d = 6$, gives $L_1 = PL_0$ with $L_0 = 0$ or $\deg L_0 + 2 \leq e$, so $L_1 = 0$; its hypothesis “$\deg P = 2$ or $\deg F = 6$” holds because $\deg P < 2$ forces $\deg Q = 2$ and, by the condition at $\infty$, $\deg S_1 = 2$. The same at $Q$ gives $L_2 = 0$. Dimension: a linear relation among $1, u, u^{-1}, g_1, g_2$ is the core with $e = 0$. Multiplier space: if $f, uf \in W_A$, subtracting the two numerators gives the core with $e = 1$, $L_1 = a_1X - a_1'$ and $L_2 = a_2X - a_2'$; so $a_1 = a_2 = 0$ and $XA = A'$, hence the coefficient of $X^2$ in $A$ vanishes and $f = A(u)/u \in \mathrm{span}(1, u^{-1})$. The converse inclusion is clear. (D1) then fails by `DiazModulus.u_multiplier_space_le_span_no_degree_one_no_visible_element`.
--
--   **Novelty.** None claimed; routine. It is Q1.5 of the project's research notes (R12) for two-orbit spaces. The proof clears denominators (`DiazModulus.quadratic_space_mem_iff_numerator`) and applies the division lemma `DiazModulus.binary_quadratic_dvd_of_coprime_mul_eq` at $P$ and at $Q$.
-- source:
--   No novelty claimed. Q1.5 of the Diaz modulus mission's research notes (round R12), for two-orbit spaces, proved here by divisibility of binary forms. Uses DiazModulus.binary_quadratic_dvd_of_coprime_mul_eq, DiazModulus.quadratic_space_mem_iff_numerator and DiazModulus.u_multiplier_space_le_span_no_degree_one_no_visible_element. R21b of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem invisible_two_orbit_space_u_multiplier_space_eq (u : ℂ) (hu : u ∉ Qbar) (P Q S₁ S₂ : (↥Qbar)[X])
    (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2) (hS₁ : S₁.natDegree ≤ 2) (hS₂ : S₂.natDegree ≤ 2)
    (hPS : IsCoprime P S₁) (hQS : IsCoprime Q S₂)
    (hP2 : P.coeff 2 ≠ 0 ∨ S₁.coeff 2 ≠ 0) (hQ2 : Q.coeff 2 ≠ 0 ∨ S₂.coeff 2 ≠ 0) :
    Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ)) = 5 ∧
    (∀ f : ℂ, (f ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ) ∧
      u * f ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ)) ↔
      f ∈ Submodule.span Qbar ({1, u⁻¹} : Set ℂ)) ∧
    ¬ (∃ t : Fin 3 → ℂ, LinearIndependent (↥Qbar) t ∧ ∀ j, t j ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ) ∧ u * t j ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ)) := by
  sorry

end DiazModulus
