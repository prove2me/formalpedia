-- Prove2me | Theorems.Thm_DiazModulus_involution_pencil_configuration_invisible_to_four_dimensional_extensions
-- name    : DiazModulus.involution_pencil_configuration_invisible_to_four_dimensional_extensions
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-10T20:24:13.114363+00:00
-- url     : https://prove2.me/theorems/542ffb79-4eab-4af6-a4b2-041826f79ece
-- title:
--   For u ∉ Q̄ with uū algebraic and any involution pencil, the space carries a 2×3 configuration while no Q̄ + Q̄u + Q̄ū + Q̄w inside it does
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$. Let $q_1, q_2 \in \overline{\mathbb{Q}}[X]$ be coprime of degree at most $2$, one of them of degree exactly $2$, so that $\Lambda = \overline{\mathbb{Q}}q_1 + \overline{\mathbb{Q}}q_2$ is the pencil of quadratics of a Möbius involution $\tau$ of the $u$-line (its members vanish on the $\tau$-orbits). Let $l_1, l_2 \in \Lambda$ be non-zero, and let $W$ be the $\overline{\mathbb{Q}}$-span of $1, u, u^{-1}$ and of $q_1(u)^iq_2(u)^{3-i}/(u\,l_1(u)l_2(u))$, $i = 0, \dots, 3$. Suppose also $\rho = u\bar u$ is algebraic, and put $H_0 = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$. Then $W$ carries a $2 \times 3$ configuration, but for no $w \in W$ outside $H_0$ does $H_0 + \overline{\mathbb{Q}}w$ carry one.
--
--   For $q_1 = X^2$, $q_2 = 1$ ($\tau: u \mapsto -u$) these are the spaces of `DiazModulus.circle_point_two_pole_configuration_invisible_to_four_dimensional_extensions` and of R5's families. Every 5-dimensional $W \supseteq \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}u^{-1}$ of rational functions of $u$ that contains a 4-term geometric progression is either of this form or contains $u^2$, $u^{-2}$ or some $1/(u - a)$; that converse is proved in the research notes and is not formalised.
--
--   **Proof.** The configuration is `DiazModulus.involution_pencil_space_carries_two_by_three_configuration`. Since $\bar u = \rho u^{-1}$, every $H_0 + \overline{\mathbb{Q}}w$ with $w \in W$ lies in $W$. If one carried a configuration with $w \notin H_0$, Theorem B (`DiazModulus.circle_point_extension_two_by_three_configuration_iff`) and exchange would put $u^2$, $\bar u^2$ or $1/(u - b)$ in $W$, and $\bar u^2 \in W$ would give $u^{-2} = \rho^{-2}\bar u^2 \in W$; `DiazModulus.involution_pencil_space_excludes_squares_and_reciprocals` rules all of them out.
--
--   **Novelty.** Not found in the sources read; it is short (Theorem B plus the exclusions). The progression step is Bachoc–Serra–Zémor (2017, Lemma 4).
-- source:
--   Not found in the sources read. Uses DiazModulus.circle_point_extension_two_by_three_configuration_iff (Theorem B of the Diaz modulus mission); the progression step is C. Bachoc, O. Serra, G. Zémor, An analogue of Vosper's theorem for extension fields, Math. Proc. Cambridge Philos. Soc. (2017), arXiv:1501.00602, Lemma 4. R9 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 10 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem involution_pencil_configuration_invisible_to_four_dimensional_extensions
    (u : ℂ) (hu : u ∉ Qbar) (q₁ q₂ l₁ l₂ : Polynomial ↥Qbar)
    (hq₁ : q₁.natDegree ≤ 2) (hq₂ : q₂.natDegree ≤ 2) (hdeg : q₁.natDegree = 2 ∨ q₂.natDegree = 2)
    (hcop : IsCoprime q₁ q₂)
    (hl₁ : l₁ ∈ Submodule.span ↥Qbar ({q₁, q₂} : Set (Polynomial ↥Qbar))) (hl₁0 : l₁ ≠ 0)
    (hl₂ : l₂ ∈ Submodule.span ↥Qbar ({q₁, q₂} : Set (Polynomial ↥Qbar))) (hl₂0 : l₂ ≠ 0) (hρ : IsAlgebraic ℚ (u * conj u)) :
    (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪ Set.range (fun i : Fin 4 =>
        Polynomial.aeval u q₁ ^ (i : ℕ) * Polynomial.aeval u q₂ ^ (3 - (i : ℕ)) /
          (u * Polynomial.aeval u l₁ * Polynomial.aeval u l₂)))) ∧
      ∀ w ∈ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪ Set.range (fun i : Fin 4 =>
        Polynomial.aeval u q₁ ^ (i : ℕ) * Polynomial.aeval u q₂ ^ (3 - (i : ℕ)) /
          (u * Polynomial.aeval u l₁ * Polynomial.aeval u l₂))),
        w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) →
        ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
          LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
  sorry

end DiazModulus
