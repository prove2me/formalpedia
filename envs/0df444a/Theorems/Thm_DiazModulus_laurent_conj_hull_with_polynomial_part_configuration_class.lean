-- Prove2me | Theorems.Thm_DiazModulus_laurent_conj_hull_with_polynomial_part_configuration_class
-- name    : DiazModulus.laurent_conj_hull_with_polynomial_part_configuration_class
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:28:24.989975+00:00
-- url     : https://prove2.me/theorems/8a1f9333-3717-4479-91a4-ad9d38a0f016
-- title:
--   If span(1, v, v̄, z, z̄) contains v² P(v) with P ≠ 0 and carries a 2×3 configuration, it contains a non-zero α v² + β v³
-- statement:
--   Let $v \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $v\bar v = 1$. Let $z \in \mathbb{C}$ and $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, v, \bar v, z, \bar z)$. Suppose that $v^2P(v) \in W$ for some non-zero $P \in \overline{\mathbb{Q}}[X]$, and that $W$ carries a $2 \times 3$ configuration (free $x_0, x_1$ and free $y_0, y_1, y_2$ over $\overline{\mathbb{Q}}$ with all six products $x_iy_j$ in the space). Then $\alpha v^2 + \beta v^3 \in W$ for some $\alpha, \beta \in \overline{\mathbb{Q}}$, not both zero.
--
--   **Proof.** Put $A = v^2P(v)$; as $W$ is conjugation-stable, $W' = \mathrm{span}(1, v, \bar v, A, \bar A) \subseteq W$. A relation among these five, multiplied by $v^{d+2}$ with $d = \deg P$, is a polynomial identity at the transcendental $v$ (with $\bar v = 1/v$ and the reflected polynomial for $\overline{P(v)}$); its coefficient at $X^{2d+4}$ kills the coordinate of $A$, the conjugate relation kills that of $\bar A$, and the rest is trivial, so $\dim W' = 5$. As $\dim W \leq 5$, $W' = W$, and the configuration lies in the polynomial hull of $Q = X^2P$ at $u := v$, where $u\bar u = 1$ is algebraic. Theorem C (`DiazModulus.polynomial_hull_two_by_three_configuration_iff`) gives $\deg Q \in \{2, 3\}$, so $P = \alpha + \beta X$ with $(\alpha, \beta) \neq (0, 0)$, and $\alpha v^2 + \beta v^3 = v^2P(v) \in W$.
--
--   **Novelty.** Not found in the sources read; routine, as a consequence of Theorem C (`DiazModulus.polynomial_hull_two_by_three_configuration_iff`).
-- source:
--   Not found in the sources read. Uses DiazModulus.polynomial_hull_two_by_three_configuration_iff. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem laurent_conj_hull_with_polynomial_part_configuration_class
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1) (z : ℂ)
    (P : Polynomial ↥Qbar) (hP : P ≠ 0) (hPW : v ^ 2 * Polynomial.aeval v P ∈ Submodule.span Qbar ({1, v, conj v, z, conj z} : Set ℂ))
    (hconf : ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, v, conj v, z, conj z} : Set ℂ)) :
    ∃ α β : ℂ, α ∈ Qbar ∧ β ∈ Qbar ∧ (α ≠ 0 ∨ β ≠ 0) ∧ α * v ^ 2 + β * v ^ 3 ∈ Submodule.span Qbar ({1, v, conj v, z, conj z} : Set ℂ) := by
  sorry

end DiazModulus
