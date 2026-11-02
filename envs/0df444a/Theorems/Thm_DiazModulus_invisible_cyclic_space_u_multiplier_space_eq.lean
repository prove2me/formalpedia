-- Prove2me | Theorems.Thm_DiazModulus_invisible_cyclic_space_u_multiplier_space_eq
-- name    : DiazModulus.invisible_cyclic_space_u_multiplier_space_eq
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-01T09:20:14.51648+00:00
-- url     : https://prove2.me/theorems/c52a9703-bf1b-47ab-ae6c-f3ed1fe68dbe
-- title:
--   Q1.5, cyclic: if S₁ has no zero in common with P, the space is five-dimensional and u keeps only span(1, 1/u) in it, so it has no degree-one triple
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $P, Q, S_1, S_2 \in \overline{\mathbb{Q}}[X]$ with $P, Q$ coprime, $\max(\deg P, \deg Q) = 2$ and $\deg S_1, \deg S_2 \leq 2$. Put $g_1 = Q(u)S_1(u)/(uP(u))$, $g_2 = Q(u)(Q(u)S_1(u) + P(u)S_2(u))/(uP(u)^2)$ and $W_B = \mathrm{span}(1, u, u^{-1}, g_1, g_2)$, the cyclic shape (D2b) of Theorem NF. Suppose that $P$ and $S_1$ have no common zero on the projective line: they are coprime, and their coefficients of $X^2$ are not both zero. Then:
--
--   - $\dim W_B = 5$;
--   - for every $f \in \mathbb{C}$, $f \in W_B$ and $uf \in W_B$ if and only if $f \in \mathrm{span}(1, u^{-1})$;
--   - (D1) fails for $W_B$: there are no linearly independent $t_0, t_1, t_2$ with $t_j, ut_j \in W_B$.
--
--   Two polynomials $P, S \in \overline{\mathbb{Q}}[X]$ of degree at most $2$ have a common zero on the projective line if they are not coprime (a common root in $\overline{\mathbb{Q}}$) or their coefficients of $X^2$ are both zero (a common zero at $\infty$, reading $P$ and $S$ as binary forms of degree $2$). When $u\bar u$ is algebraic, `DiazModulus.cyclic_space_visible_to_four_dimensional_extensions_iff_common_zero` says that the condition on $S_1$ is exactly the invisibility of $W_B$ to the four-dimensional extensions; it is stated directly, so that neither $u\bar u$ nor complex conjugation enters. So an invisible cyclic space has no degree-one triple. Every position of the orbits is covered by the same argument: a zero at $0$ or at $\infty$, a double zero, and $P$ or $Q$ constant.
--
--   **Proof.** By `DiazModulus.quadratic_space_mem_iff_numerator`, $f \in W_B$ means $f\,uP(u)^2 = (P^2A + a_1PQS_1 + a_2Q(QS_1 + PS_2))(u)$ with $\deg A \leq 2$. **Core:** if $P^2A + PQS_1L_1 + Q(QS_1 + PS_2)L_2 = 0$ with $\deg L_i \leq e \leq 1$ and $\deg A \leq 2 + e$, then $L_1 = L_2 = 0$. Indeed $Q^2S_1L_2 = -P(PA + QS_1L_1 + QS_2L_2)$, and `DiazModulus.binary_quadratic_dvd_of_coprime_mul_eq` at $P$ with $F = Q^2S_1$, $d = 6$ gives $L_2 = 0$ (the right-hand factor has degree at most $4 + e$ because $\deg S_2 \leq 2$). Then $PA + QS_1L_1 = 0$, and `DiazModulus.binary_quadratic_dvd_of_coprime_mul_eq` with $F = QS_1$, $d = 4$ gives $L_1 = 0$. The hypothesis “$\deg P = 2$ or $\deg F = d$” holds because $\deg P < 2$ forces $\deg Q = 2$ and, by the condition at $\infty$, $\deg S_1 = 2$. The dimension, the multiplier space and the failure of (D1) follow as in the two-orbit case (`DiazModulus.invisible_two_orbit_space_u_multiplier_space_eq`), with `DiazModulus.u_multiplier_space_le_span_no_degree_one_no_visible_element`.
--
--   **Novelty.** None claimed; routine. It is Q1.5 of the project's research notes (R12) for cyclic spaces. The proof clears denominators (`DiazModulus.quadratic_space_mem_iff_numerator`) and applies the division lemma `DiazModulus.binary_quadratic_dvd_of_coprime_mul_eq` twice at $P$.
-- source:
--   No novelty claimed. Q1.5 of the Diaz modulus mission's research notes (round R12), for cyclic spaces, proved here by divisibility of binary forms. Uses DiazModulus.binary_quadratic_dvd_of_coprime_mul_eq, DiazModulus.quadratic_space_mem_iff_numerator and DiazModulus.u_multiplier_space_le_span_no_degree_one_no_visible_element. R21b of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem invisible_cyclic_space_u_multiplier_space_eq (u : ℂ) (hu : u ∉ Qbar) (P Q S₁ S₂ : (↥Qbar)[X])
    (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2) (hS₁ : S₁.natDegree ≤ 2) (hS₂ : S₂.natDegree ≤ 2)
    (hPS : IsCoprime P S₁) (hP2 : P.coeff 2 ≠ 0 ∨ S₁.coeff 2 ≠ 0) :
    Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ)) = 5 ∧
    (∀ f : ℂ, (f ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ) ∧
      u * f ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ)) ↔
      f ∈ Submodule.span Qbar ({1, u⁻¹} : Set ℂ)) ∧
    ¬ (∃ t : Fin 3 → ℂ, LinearIndependent (↥Qbar) t ∧ ∀ j, t j ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ) ∧ u * t j ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ)) := by
  sorry

end DiazModulus
