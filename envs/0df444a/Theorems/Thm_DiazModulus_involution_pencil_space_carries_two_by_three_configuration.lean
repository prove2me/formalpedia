-- Prove2me | Theorems.Thm_DiazModulus_involution_pencil_space_carries_two_by_three_configuration
-- name    : DiazModulus.involution_pencil_space_carries_two_by_three_configuration
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-10T20:24:14.93821+00:00
-- url     : https://prove2.me/theorems/b372d03d-7bb5-469f-93a0-efc25a44f423
-- title:
--   For u ∉ Q̄ and the pencil of any Möbius involution, the space Q̄ + Q̄u + Q̄u⁻¹ + Σ Q̄ q₁(u)ⁱq₂(u)³⁻ⁱ/(u l₁(u)l₂(u)) carries a 2×3 configuration
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$. Let $q_1, q_2 \in \overline{\mathbb{Q}}[X]$ be coprime of degree at most $2$, one of them of degree exactly $2$, so that $\Lambda = \overline{\mathbb{Q}}q_1 + \overline{\mathbb{Q}}q_2$ is the pencil of quadratics of a Möbius involution $\tau$ of the $u$-line (its members vanish on the $\tau$-orbits). Let $l_1, l_2 \in \Lambda$ be non-zero, and let $W$ be the $\overline{\mathbb{Q}}$-span of $1, u, u^{-1}$ and of $q_1(u)^iq_2(u)^{3-i}/(u\,l_1(u)l_2(u))$, $i = 0, \dots, 3$. Then there are $x_1, x_2$, free over $\overline{\mathbb{Q}}$, and $y_1, y_2, y_3$, free over $\overline{\mathbb{Q}}$, with all six products $x_iy_j$ in $W$: $W$ contains the progression $c, cr, cr^2, cr^3$ with ratio $r = q_1(u)/q_2(u)$.
--
--   **Proof.** Put $r = q_1(u)/q_2(u)$ and $c = q_2(u)^3/(u\,l_1(u)l_2(u))$; then $c\,r^k$, $k = 0, \dots, 3$, are the four extra spanning elements, so $x = (1, r)$, $y = (c, cr, cr^2)$ has all six products in $W$. Since $u$ is transcendental, $q_2(u)$, $l_i(u)$ and $u$ are non-zero, and $r \notin \overline{\mathbb{Q}}$: otherwise $q_1 = r q_2$ as polynomials, against coprimality and the degree condition. So $r$ is transcendental, and $1, r, r^2$ are free.
--
--   **Novelty.** Not asserted for the shape: it is the progression of Fischler (2001, Lemma 6.1) and Diaz (2007, Th. 7(2)); that a configuration whose products span four dimensions is a progression is Bachoc–Serra–Zémor (2017, Lemma 4).
-- source:
--   The configuration is the progression of S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Lemma 6.1 (p. 184), and G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Th. 7(2) (p. 390). R9 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 10 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem involution_pencil_space_carries_two_by_three_configuration
    (u : ℂ) (hu : u ∉ Qbar) (q₁ q₂ l₁ l₂ : Polynomial ↥Qbar)
    (hq₁ : q₁.natDegree ≤ 2) (hq₂ : q₂.natDegree ≤ 2) (hdeg : q₁.natDegree = 2 ∨ q₂.natDegree = 2)
    (hcop : IsCoprime q₁ q₂)
    (hl₁ : l₁ ∈ Submodule.span ↥Qbar ({q₁, q₂} : Set (Polynomial ↥Qbar))) (hl₁0 : l₁ ≠ 0)
    (hl₂ : l₂ ∈ Submodule.span ↥Qbar ({q₁, q₂} : Set (Polynomial ↥Qbar))) (hl₂0 : l₂ ≠ 0) :
    ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪ Set.range (fun i : Fin 4 =>
        Polynomial.aeval u q₁ ^ (i : ℕ) * Polynomial.aeval u q₂ ^ (3 - (i : ℕ)) /
          (u * Polynomial.aeval u l₁ * Polynomial.aeval u l₂))) := by
  sorry

end DiazModulus
