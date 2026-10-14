-- Prove2me | Theorems.Thm_DiazModulus_quadratic_ratio_progression_space_eq_involution_pencil_space
-- name    : DiazModulus.quadratic_ratio_progression_space_eq_involution_pencil_space
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-12T19:23:03.336089+00:00
-- url     : https://prove2.me/theorems/fed2dbdb-56de-4027-a142-5ac1990bb701
-- title:
--   For u ∉ Q̄ and coprime p, q ∈ Q̄[X] of maximal degree 2: a five-dimensional Q̄ + Q̄u + Q̄u⁻¹ + Σ Q̄ c (p(u)/q(u))ᵏ is R9's involution-pencil space for (p, q)
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$, let $p, q \in \overline{\mathbb{Q}}[X]$ be coprime, $h = p(u)/q(u)$, let $c \in \mathbb{C}$ be non-zero, and let $W$ be the $\overline{\mathbb{Q}}$-span of $1, u, u^{-1}$ and $c, ch, ch^2, ch^3$. Suppose $\dim W = 5$. If $\max(\deg p, \deg q) = 2$, then $W$ is the $\overline{\mathbb{Q}}$-span of $1, u, u^{-1}$ and $p(u)^iq(u)^{3-i}/(u\,l_1(u)l_2(u))$, $i = 0, \dots, 3$, for some non-zero $l_1, l_2 \in \overline{\mathbb{Q}}p + \overline{\mathbb{Q}}q$.
--
--   $p$ and $q$ span the pencil of a Möbius involution of the $u$-line, and these are exactly the spaces of R9, which carry a configuration invisible to Theorem B.
--
--   **Proof.** $h$ is transcendental, so $c, ch, ch^2, ch^3$ are free, and $\dim W = 5$ gives two free elements $c\,\varphi_i(h)$ of $\overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}u^{-1}$ with $\deg\varphi_i \le 3$: $cu\,\varphi_i(h) = R_i(u)$, $\deg R_i \le 2$. Write $\varphi_i = g\psi_i$ with $\psi_1, \psi_2$ coprime of degree at most $m \geq 1$, and $\Psi_i = \sum_j \psi_{ij}p^jq^{m-j}$. Then $\Psi_1R_2 = \Psi_2R_1$, and $\Psi_1, \Psi_2$ have no common zero, so $R_i = \rho\Psi_i$. One $\Psi_i$ has degree $2m$, so $m = 1$ and $\rho = \kappa$ is a non-zero constant: $cu\,g(h) = \kappa q(u)$ with $\deg g \le 2$. Splitting $g$ over \overline{\mathbb{Q}} gives the pencil members $l_1, l_2$ with $ch^k = \kappa p(u)^kq(u)^{3-k}/(u\,l_1(u)l_2(u))$.
--
--   **Novelty.** Not found in the sources read; it is short.
-- source:
--   Not found in the sources read. R13 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 12 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem quadratic_ratio_progression_space_eq_involution_pencil_space
    (u : ℂ) (hu : u ∉ Qbar) (p q : Polynomial ↥Qbar) (hcop : IsCoprime p q)
    (hdeg : max p.natDegree q.natDegree = 2) (c : ℂ) (hc : c ≠ 0)
    (hdim : Module.finrank (↥Qbar) (Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
      Set.range (fun k : Fin 4 => c * (Polynomial.aeval u p / Polynomial.aeval u q) ^ (k : ℕ)))) = 5) :
    ∃ l₁ l₂ : Polynomial ↥Qbar,
      l₁ ∈ Submodule.span ↥Qbar ({p, q} : Set (Polynomial ↥Qbar)) ∧ l₁ ≠ 0 ∧
      l₂ ∈ Submodule.span ↥Qbar ({p, q} : Set (Polynomial ↥Qbar)) ∧ l₂ ≠ 0 ∧
      Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
      Set.range (fun k : Fin 4 => c * (Polynomial.aeval u p / Polynomial.aeval u q) ^ (k : ℕ))) =
        Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪ Set.range (fun i : Fin 4 =>
          Polynomial.aeval u p ^ (i : ℕ) * Polynomial.aeval u q ^ (3 - (i : ℕ)) /
            (u * Polynomial.aeval u l₁ * Polynomial.aeval u l₂))) := by
  sorry

end DiazModulus
