-- Prove2me | Theorems.Thm_DiazModulus_laurent_conj_hull_without_polynomial_part_configuration_classes
-- name    : DiazModulus.laurent_conj_hull_without_polynomial_part_configuration_classes
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:28:28.365988+00:00
-- url     : https://prove2.me/theorems/fcaf2ffd-cfe3-49ca-8f97-31a0147fb82b
-- title:
--   A five-dimensional Laurent hull span(1, v, v̄, z, z̄) without v² P(v) in it carries a 2×3 configuration only in the involution or real pencil normal form
-- statement:
--   Let $v \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $v\bar v = 1$. Let $k \geq 0$, let $c_j \in \overline{\mathbb{Q}}$ for all $j \in \mathbb{Z}$, and put $z = \sum_{j=-k}^{k} c_jv^j$ and $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, v, \bar v, z, \bar z)$. Suppose $\dim_{\overline{\mathbb{Q}}} W = 5$, $W$ contains no $v^2P(v)$ with $P \in \overline{\mathbb{Q}}[X]$ non-zero, and $W$ carries a $2 \times 3$ configuration (free $x_0, x_1$ and free $y_0, y_1, y_2$ over $\overline{\mathbb{Q}}$ with all six products $x_iy_j$ in the space). Then $W$ is in one of the two classes
--
--   - **(Q)** $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, v, \bar v, \bar v^2 + ev^2, \beta\bar v^3 + \zeta v^2 + ev^3)$ for some $e, \beta, \zeta \in \overline{\mathbb{Q}}$ with $e\bar e = 1$, $\beta\bar\beta = 1$ and $\zeta = -\beta e^2\bar\zeta$;
--   - **(R)** $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, v, \bar v, g, \bar g)$ with $g = G(v) + \kappa\,\overline{vG(v)}$, for some $\kappa \in \overline{\mathbb{Q}}$ with $\kappa\bar\kappa = 1$ and some $G \in \overline{\mathbb{Q}}[X]$ with $G(0) = 0$ and $\deg G \geq 2$.
--
--   **Proof.** The shifted polynomial model (`DiazModulus.laurent_conj_hull_shifted_polynomial_model`) writes $W$ as the image of $H_N + M$ under $\Phi : F \mapsto F(v)/v^N$, with $M$ two-sided. A configuration $x \otimes y$ in $W$ factors (`DiazModulus.config_shifted_coprime_polynomial_factors`) through coprime $a_0, a_1$ and free $b_0, b_1, b_2$ with $a_ib_j \in H_N + M$ and $x_1a_0(v) = x_0a_1(v)$; as $x$ is free the ratio is not constant, `DiazModulus.two_by_three_configuration_ratio_degree_le_two` bounds its degree by two, `DiazModulus.coprime_pencil_of_degree_le_two_normal_form` leaves four pencils, and `DiazModulus.laurent_window_quadratic_pencils_carry_no_three_factors` rules out $(1, X^2 + \alpha X)$ and $(X + \beta, X^2 + \gamma X)$. For $(1, X)$, `DiazModulus.laurent_window_degree_one_pencil_factor_space` gives $W = \mathrm{span}(1, v, \bar v, g, vg)$ with $g = \Phi(G_0)$; conjugation-stability of $W$ and the factor-space property give $\bar g \in \mathrm{span}(1, v, vg)$, and `DiazModulus.laurent_degree_one_conj_stable_space_real_pencil_normal_form` gives class (R), as $v^2 \notin W$ excludes $\deg G \leq 1$. For $(X, X^2 + \beta)$, `DiazModulus.laurent_window_involution_pencil_normal_form` puts $M$ in the involution normal form, $\Phi$ carries it to $\mathrm{span}(1, v, \bar v, \bar v^2 + ev^2, \beta\bar v^3 + \zeta v^2 + ev^3)$, and `DiazModulus.laurent_involution_space_conj_stable_constraints` gives the constraints of class (Q).
--
--   **Novelty.** Not found in the sources read. It is most of the "only if" half of Theorem E (`DiazModulus.laurent_conj_hull_two_by_three_configuration_iff`); given its children, routine.
-- source:
--   Not found in the sources read. Uses DiazModulus.laurent_conj_hull_shifted_polynomial_model, DiazModulus.config_shifted_coprime_polynomial_factors, DiazModulus.two_by_three_configuration_ratio_degree_le_two, DiazModulus.coprime_pencil_of_degree_le_two_normal_form, DiazModulus.laurent_window_quadratic_pencils_carry_no_three_factors, DiazModulus.laurent_window_degree_one_pencil_factor_space, DiazModulus.laurent_window_involution_pencil_normal_form, DiazModulus.laurent_degree_one_conj_stable_space_real_pencil_normal_form and DiazModulus.laurent_involution_space_conj_stable_constraints. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem laurent_conj_hull_without_polynomial_part_configuration_classes
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1) (k : ℕ) (c : ℤ → ℂ) (hc : ∀ j, c j ∈ Qbar)
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, v, conj v, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j)} : Set ℂ)) = 5)
    (hB : ∀ P : Polynomial ↥Qbar, v ^ 2 * Polynomial.aeval v P ∈ Submodule.span Qbar ({1, v, conj v, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j)} : Set ℂ) → P = 0)
    (hconf : ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, v, conj v, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j)} : Set ℂ)) :
    (∃ e β ζ : ℂ, e ∈ Qbar ∧ β ∈ Qbar ∧ ζ ∈ Qbar ∧ e * conj e = 1 ∧ β * conj β = 1 ∧
        ζ = -(β * e ^ 2 * conj ζ) ∧
        Submodule.span Qbar ({1, v, conj v, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j)} : Set ℂ) =
          Submodule.span Qbar ({1, v, conj v, conj v ^ 2 + e * v ^ 2, β * conj v ^ 3 + ζ * v ^ 2 + e * v ^ 3} : Set ℂ)) ∨
      (∃ κ : ℂ, κ ∈ Qbar ∧ κ * conj κ = 1 ∧ ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧ 2 ≤ G.natDegree ∧
        Submodule.span Qbar ({1, v, conj v, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j)} : Set ℂ) =
          Submodule.span Qbar ({1, v, conj v, Polynomial.aeval v G + κ * conj (v * Polynomial.aeval v G), conj (Polynomial.aeval v G + κ * conj (v * Polynomial.aeval v G))} : Set ℂ)) := by
  sorry

end DiazModulus
