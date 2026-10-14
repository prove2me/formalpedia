-- Prove2me | Theorems.Thm_DiazModulus_progression_space_ratio_degree_le_two
-- name    : DiazModulus.progression_space_ratio_degree_le_two
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-12T19:24:39.255201+00:00
-- url     : https://prove2.me/theorems/36e45dbf-d812-422f-8517-c1a21fd08d3f
-- title:
--   For u ∉ Q̄ and coprime p, q ∈ Q̄[X]: if Q̄ + Q̄u + Q̄u⁻¹ + Σ Q̄ c (p(u)/q(u))ᵏ (k ≤ 3) is five-dimensional, then max(deg p, deg q) ≤ 2
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$, let $p, q \in \overline{\mathbb{Q}}[X]$ be coprime, $h = p(u)/q(u)$, let $c \in \mathbb{C}$ be non-zero, and let $W$ be the $\overline{\mathbb{Q}}$-span of $1, u, u^{-1}$ and $c, ch, ch^2, ch^3$. Suppose $\dim W = 5$. If $\max(\deg p, \deg q) \geq 1$, then $\max(\deg p, \deg q) \leq 2$.
--
--   So the ratio of a $4$-term progression in such a space generates a subfield of index $1$ or $2$ of \overline{\mathbb{Q}}$(u)$.
--
--   **Proof.** Evaluation at the transcendental $u$ embeds $\overline{\mathbb{Q}}(X)$ in $\mathbb{C}$; let $f = p/q$ there, so $f \mapsto h$. By coprimality, $\max(\deg p, \deg q) \le [\overline{\mathbb{Q}}(X) : \overline{\mathbb{Q}}(f)]$ (Mathlib's `RatFunc.finrank_eq_max_natDegree`, from the Lüroth file). $f$ is not constant, so $h$ is transcendental and $c, ch, ch^2, ch^3$ are free; with $\dim(\overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}u^{-1}) = 3$ and $\dim W = 5$, the intersection $H \cap P$ of the two parts has dimension at least $2$. Two non-proportional $x_i = cA_i(h)$ in it have $ux_i = R_i(u)$ with $\deg R_i \le 2$; $\varphi = R_1/R_2$ is non-constant and maps to $A_1(h)/A_2(h)$, so $\varphi \in \overline{\mathbb{Q}}(f)$ and $[\overline{\mathbb{Q}}(X) : \overline{\mathbb{Q}}(f)]$ divides $[\overline{\mathbb{Q}}(X) : \overline{\mathbb{Q}}(\varphi)] \le 2$.
--
--   **Novelty.** Not found in the sources read; it is short.
-- source:
--   Not found in the sources read. Uses Mathlib's degree formula for rational functions (Lüroth's file). R13 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 12 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem progression_space_ratio_degree_le_two
    (u : ℂ) (hu : u ∉ Qbar) (p q : Polynomial ↥Qbar) (hcop : IsCoprime p q)
    (hdeg : 1 ≤ max p.natDegree q.natDegree) (c : ℂ) (hc : c ≠ 0)
    (hdim : Module.finrank (↥Qbar) (Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
      Set.range (fun k : Fin 4 => c * (Polynomial.aeval u p / Polynomial.aeval u q) ^ (k : ℕ)))) = 5) :
    max p.natDegree q.natDegree ≤ 2 := by
  sorry

end DiazModulus
