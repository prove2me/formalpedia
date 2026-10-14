-- Prove2me | Theorems.Thm_DiazModulus_progression_space_contains_square_or_reciprocal_or_eq_involution_pencil_space
-- name    : DiazModulus.progression_space_contains_square_or_reciprocal_or_eq_involution_pencil_space
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-12T19:22:58.516196+00:00
-- url     : https://prove2.me/theorems/d2501f32-e51d-4d24-be11-d86a26332da9
-- title:
--   For u ∉ Q̄ and coprime p, q ∈ Q̄[X]: a five-dimensional Q̄ + Q̄u + Q̄u⁻¹ + Σ Q̄ c (p(u)/q(u))ᵏ contains u², u⁻² or some 1/(u − b), or is R9's involution space
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$, let $p, q \in \overline{\mathbb{Q}}[X]$ be coprime, $h = p(u)/q(u)$, let $c \in \mathbb{C}$ be non-zero, and let $W$ be the $\overline{\mathbb{Q}}$-span of $1, u, u^{-1}$ and $c, ch, ch^2, ch^3$. Suppose $\dim W = 5$. If $\max(\deg p, \deg q) \geq 1$, then $W$ contains $u^2$, $u^{-2}$ or $1/(u - b)$ for some non-zero $b \in \overline{\mathbb{Q}}$, or $W$ is the $\overline{\mathbb{Q}}$-span of $1, u, u^{-1}$ and $p(u)^iq(u)^{3-i}/(u\,l_1(u)l_2(u))$, $i = 0, \dots, 3$, for some non-zero $l_1, l_2 \in \overline{\mathbb{Q}}p + \overline{\mathbb{Q}}q$.
--
--   Together with `DiazModulus.mobius_progression_space_contains_square_or_reciprocal` (ratio of degree $1$) and R9's `DiazModulus.involution_pencil_configuration_invisible_to_four_dimensional_extensions` (ratio of degree $2$), this classifies the five-dimensional spaces $W \supseteq \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}u^{-1}$ that contain a $4$-term geometric progression with rational ratio: either $W$ contains $u^2$, $u^{-2}$ or some $1/(u - b)$, or $W$ is one of R9's involution spaces, which contain none of them.
--
--   **Proof.** By `DiazModulus.progression_space_ratio_degree_le_two` the ratio has degree $1$ or $2$. In degree $1$, $h = (\alpha u + \beta)/(\gamma u + \delta)$ with $\alpha\delta - \beta\gamma \neq 0$ by coprimality, and `DiazModulus.mobius_progression_space_contains_square_or_reciprocal` gives $u^2$, $u^{-2}$ or some $1/(u - b)$ in $W$. In degree $2$, `DiazModulus.quadratic_ratio_progression_space_eq_involution_pencil_space` gives R9's form.
--
--   **Novelty.** Not found in the sources read; it is short. That a configuration whose six products span four dimensions is such a progression is Bachoc–Serra–Zémor (2017, Lemma 4); here the progression is a hypothesis.
-- source:
--   Not found in the sources read. The progression step, not used here, is C. Bachoc, O. Serra, G. Zémor, An analogue of Vosper's theorem for extension fields, Math. Proc. Cambridge Philos. Soc. (2017), arXiv:1501.00602, Lemma 4. R13 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 12 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem progression_space_contains_square_or_reciprocal_or_eq_involution_pencil_space
    (u : ℂ) (hu : u ∉ Qbar) (p q : Polynomial ↥Qbar) (hcop : IsCoprime p q)
    (hdeg : 1 ≤ max p.natDegree q.natDegree) (c : ℂ) (hc : c ≠ 0)
    (hdim : Module.finrank (↥Qbar) (Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
      Set.range (fun k : Fin 4 => c * (Polynomial.aeval u p / Polynomial.aeval u q) ^ (k : ℕ)))) = 5) :
    (u ^ 2 ∈ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
      Set.range (fun k : Fin 4 => c * (Polynomial.aeval u p / Polynomial.aeval u q) ^ (k : ℕ))) ∨
      (u ^ 2)⁻¹ ∈ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
      Set.range (fun k : Fin 4 => c * (Polynomial.aeval u p / Polynomial.aeval u q) ^ (k : ℕ))) ∨
      ∃ b ∈ Qbar, b ≠ 0 ∧ (u - b)⁻¹ ∈ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
      Set.range (fun k : Fin 4 => c * (Polynomial.aeval u p / Polynomial.aeval u q) ^ (k : ℕ)))) ∨
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
