-- Prove2me | Theorems.Thm_DiazModulus_involution_pencil_space_excludes_squares_and_reciprocals
-- name    : DiazModulus.involution_pencil_space_excludes_squares_and_reciprocals
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-10T20:24:14.599737+00:00
-- url     : https://prove2.me/theorems/212fc5e4-7258-42d6-acf0-73a839f920c5
-- title:
--   For the same u and any involution pencil, the space contains none of u², u⁻² and 1/(u − b) with b ∈ Q̄ non-zero
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$. Let $q_1, q_2 \in \overline{\mathbb{Q}}[X]$ be coprime of degree at most $2$, one of them of degree exactly $2$, so that $\Lambda = \overline{\mathbb{Q}}q_1 + \overline{\mathbb{Q}}q_2$ is the pencil of quadratics of a Möbius involution $\tau$ of the $u$-line (its members vanish on the $\tau$-orbits). Let $l_1, l_2 \in \Lambda$ be non-zero, and let $W$ be the $\overline{\mathbb{Q}}$-span of $1, u, u^{-1}$ and of $q_1(u)^iq_2(u)^{3-i}/(u\,l_1(u)l_2(u))$, $i = 0, \dots, 3$. Then $W$ contains none of $u^2$, $u^{-2}$ and $1/(u - b)$ for non-zero $b \in \overline{\mathbb{Q}}$.
--
--   For $q_1 = X^2$, $q_2 = 1$ ($\tau: u \mapsto -u$) these are the spaces of `DiazModulus.circle_point_two_pole_configuration_invisible_to_four_dimensional_extensions` and of R5's families. Every 5-dimensional $W \supseteq \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}u^{-1}$ of rational functions of $u$ that contains a 4-term geometric progression is either of this form or contains $u^2$, $u^{-2}$ or some $1/(u - a)$; that converse is proved in the research notes and is not formalised.
--
--   **Proof.** Write the involution explicitly: with $A, B, \Gamma$ the Plücker coordinates of the pencil and $D = A^2 + B\Gamma$ (non-zero by coprimality), $\tau(X) = (AX + B)/(\Gamma X - A)$ and $n^2 q(\tau u) = D\,q(u)$ for $q \in \Lambda$, $n = \Gamma u - A$. A membership, cleared of denominators, becomes $N(u)L(u) = (u - \beta)(Q(u)L(u) + S(u))$ with $N(\beta) \neq 0$ ($u^{-2}$: $\beta = 0$; $1/(u - b)$: $\beta = b$; $u^2$: the same for $1/u$ with the reversed quadratics). As $u$ is transcendental it is a polynomial identity, so it holds at $\tau(u)$ too; eliminating $S$ gives a polynomial vanishing at $u$, hence identically, which forces $\beta$ to be a fixed point of $\tau$ and then $D = 0$, a contradiction.
--
--   **Novelty.** Not found in the sources read; it is short (the involution splits a membership into even and odd parts).
-- source:
--   Not found in the sources read; generalises the parity argument of R5 and R7 from u ↦ −u to every Möbius involution. R9 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 10 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem involution_pencil_space_excludes_squares_and_reciprocals
    (u : ℂ) (hu : u ∉ Qbar) (q₁ q₂ l₁ l₂ : Polynomial ↥Qbar)
    (hq₁ : q₁.natDegree ≤ 2) (hq₂ : q₂.natDegree ≤ 2) (hdeg : q₁.natDegree = 2 ∨ q₂.natDegree = 2)
    (hcop : IsCoprime q₁ q₂)
    (hl₁ : l₁ ∈ Submodule.span ↥Qbar ({q₁, q₂} : Set (Polynomial ↥Qbar))) (hl₁0 : l₁ ≠ 0)
    (hl₂ : l₂ ∈ Submodule.span ↥Qbar ({q₁, q₂} : Set (Polynomial ↥Qbar))) (hl₂0 : l₂ ≠ 0) :
    u ^ 2 ∉ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪ Set.range (fun i : Fin 4 =>
        Polynomial.aeval u q₁ ^ (i : ℕ) * Polynomial.aeval u q₂ ^ (3 - (i : ℕ)) /
          (u * Polynomial.aeval u l₁ * Polynomial.aeval u l₂))) ∧
      (u ^ 2)⁻¹ ∉ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪ Set.range (fun i : Fin 4 =>
        Polynomial.aeval u q₁ ^ (i : ℕ) * Polynomial.aeval u q₂ ^ (3 - (i : ℕ)) /
          (u * Polynomial.aeval u l₁ * Polynomial.aeval u l₂))) ∧
      ∀ b ∈ Qbar, b ≠ 0 → (u - b)⁻¹ ∉ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪ Set.range (fun i : Fin 4 =>
        Polynomial.aeval u q₁ ^ (i : ℕ) * Polynomial.aeval u q₂ ^ (3 - (i : ℕ)) /
          (u * Polynomial.aeval u l₁ * Polynomial.aeval u l₂))) := by
  sorry

end DiazModulus
