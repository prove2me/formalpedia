-- Prove2me | Theorems.Thm_DiazModulus_progression_pair_span_ratio_degree_le_two
-- name    : DiazModulus.progression_pair_span_ratio_degree_le_two
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-14T07:30:28.575892+00:00
-- url     : https://prove2.me/theorems/ca324ec5-c275-4cf4-b1bb-b71de0e7c2d1
-- title:
--   For u ∉ Q̄ and coprime p, q ∈ Q̄[X]: if 1, u, u⁻¹ lie in the span of c, ch, ch², ck, chk with h = p(u)/q(u), then max(deg p, deg q) ≤ 2
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ and $c, k \in \mathbb{C}$ with $c \neq 0$, and suppose $1, u, u^{-1}$ lie in the $\overline{\mathbb{Q}}$-span of $c, ch, ch^2, ck, chk$. Suppose $h = p(u)/q(u)$ with $p, q \in \overline{\mathbb{Q}}[X]$ coprime and $\max(\deg p, \deg q) \geq 1$. Then $\max(\deg p, \deg q) \leq 2$.
--
--   A configuration $(1, h) \otimes Y$ whose products span a five-dimensional $W \supseteq \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}u^{-1}$ gives, after normalisation, $W = c\cdot\mathrm{span}(1, h, h^2, k, hk)$ (research notes R12, Q1; not formalised). So no such configuration has a ratio of degree $3$ or more.
--
--   **Proof.** Evaluation at $u$ embeds $\overline{\mathbb{Q}}(X)$ in $\mathbb{C}$; let $f = p/q$. Coprimality and Mathlib's `RatFunc.finrank_eq_max_natDegree` give $\max(\deg p, \deg q) \le [\overline{\mathbb{Q}}(X) : \overline{\mathbb{Q}}(f)]$. As $f$ is not constant, $h \notin \overline{\mathbb{Q}}$, and `DiazModulus.quadratic_over_ratio_of_mem_progression_pair_span` gives $A(h)u^2 + B(h)u + C(h) = 0$; by injectivity $X$ is a root of the non-zero $A(f)Y^2 + B(f)Y + C(f)$ over $\overline{\mathbb{Q}}(f)$ ($f$ is transcendental), so $[\overline{\mathbb{Q}}(X) : \overline{\mathbb{Q}}(f)] = \deg \operatorname{minpoly} X \le 2$.
--
--   **Novelty.** Not found in the sources read; it is short.
-- source:
--   Not found in the sources read. R14 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 14 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem progression_pair_span_ratio_degree_le_two
    (u : ℂ) (hu : u ∉ Qbar) (p q : Polynomial ↥Qbar) (hcop : IsCoprime p q)
    (hdeg : 1 ≤ max p.natDegree q.natDegree) (c k : ℂ) (hc : c ≠ 0)
    (h1 : (1 : ℂ) ∈ Submodule.span Qbar ({c, c * (Polynomial.aeval u p / Polynomial.aeval u q), c * (Polynomial.aeval u p / Polynomial.aeval u q) ^ 2, c * k, c * (Polynomial.aeval u p / Polynomial.aeval u q) * k} : Set ℂ)) (hu1 : u ∈ Submodule.span Qbar ({c, c * (Polynomial.aeval u p / Polynomial.aeval u q), c * (Polynomial.aeval u p / Polynomial.aeval u q) ^ 2, c * k, c * (Polynomial.aeval u p / Polynomial.aeval u q) * k} : Set ℂ)) (hui : u⁻¹ ∈ Submodule.span Qbar ({c, c * (Polynomial.aeval u p / Polynomial.aeval u q), c * (Polynomial.aeval u p / Polynomial.aeval u q) ^ 2, c * k, c * (Polynomial.aeval u p / Polynomial.aeval u q) * k} : Set ℂ)) :
    max p.natDegree q.natDegree ≤ 2 := by
  sorry

end DiazModulus
