-- Prove2me | Theorems.Thm_DiazModulus_laurent_conj_hull_finrank_le_four_no_two_by_three_configuration
-- name    : DiazModulus.laurent_conj_hull_finrank_le_four_no_two_by_three_configuration
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:28:21.544375+00:00
-- url     : https://prove2.me/theorems/9ab24c16-a6ac-4815-8560-a85922b54050
-- title:
--   The hull span(1, v, v̄, z, z̄) of a Laurent polynomial z in v, if of dimension at most four, carries no 2×3 configuration
-- statement:
--   Let $v \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $v\bar v = 1$. Let $k \geq 0$, let $c_j \in \overline{\mathbb{Q}}$ for all $j \in \mathbb{Z}$, and put $z = \sum_{j=-k}^{k} c_jv^j$ and $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, v, \bar v, z, \bar z)$. If $\dim_{\overline{\mathbb{Q}}} W \leq 4$, then $W$ carries no $2 \times 3$ configuration (free $x_0, x_1$ and free $y_0, y_1, y_2$ over $\overline{\mathbb{Q}}$ with all six products $x_iy_j$ in the space).
--
--   **Proof.** Let $H_0 = \mathrm{span}(1, v, \bar v)$. If $z \in H_0$, then $\bar z \in H_0$ and $W \subseteq H_0$, the polynomial hull of $P = 0$, where Theorem C(iii) (`DiazModulus.polynomial_hull_no_two_by_three_configuration`) excludes a configuration. Otherwise $1, v, \bar v, z$ are free, so $W = H_0 + \overline{\mathbb{Q}}z$ has dimension $4$, and a configuration would, by Theorem B (`DiazModulus.circle_point_extension_two_by_three_configuration_iff`), put $z$ in $H_0 + \overline{\mathbb{Q}}w$ with a non-zero coefficient $\delta$ on some $w \in \{v^2, \bar v^2, (v - a)^{-1}\}$, $a \neq 0$. For $w = v^2$ or $\bar v^2$, the relation $\bar z \in \mathrm{span}(1, v, \bar v, z)$ times $v^2$ is a quartic identity at the transcendental $v$ whose constant, resp. top, coefficient is $\bar\delta$, so $\delta = 0$. For $w = (v - a)^{-1}$, $v^kz = F(v)$ gives $X(X - a)F = (X - a)B + \delta X^{k+1}$ in $\overline{\mathbb{Q}}[X]$, which at $X = a$ reads $0 = \delta a^{k+1}$.
--
--   **Novelty.** Not found in the sources read; routine, as a consequence of Theorem B (`DiazModulus.circle_point_extension_two_by_three_configuration_iff`) and Theorem C(iii) (`DiazModulus.polynomial_hull_no_two_by_three_configuration`).
-- source:
--   Not found in the sources read. Uses DiazModulus.circle_point_extension_two_by_three_configuration_iff and DiazModulus.polynomial_hull_no_two_by_three_configuration. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem laurent_conj_hull_finrank_le_four_no_two_by_three_configuration
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1) (k : ℕ) (c : ℤ → ℂ) (hc : ∀ j, c j ∈ Qbar)
    (h4 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, v, conj v, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j)} : Set ℂ)) ≤ 4) :
    ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, v, conj v, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j)} : Set ℂ) := by
  sorry

end DiazModulus
