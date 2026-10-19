-- Prove2me | Theorems.Thm_DiazModulus_laurent_conj_hull_two_by_three_configuration_iff
-- name    : DiazModulus.laurent_conj_hull_two_by_three_configuration_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:28:27.86101+00:00
-- url     : https://prove2.me/theorems/ca560c9f-536b-489e-a9c3-02cc24d09324
-- title:
--   Theorem E: the conjugation hull of a polynomial in u and ū carries a 2×3 configuration exactly when it is five-dimensional and in the polynomial, involution or real pencil class
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ and $s \in \overline{\mathbb{Q}}$ with $s^2 = u\bar u$ (so $s = \pm|u|$ is real), and put $v = u/s$, so that $\bar v = 1/v$. Let $k \geq 0$, let $c_j \in \overline{\mathbb{Q}}$ for all $j \in \mathbb{Z}$, and put $z = \sum_{j=-k}^{k} c_jv^j$ and $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, u, \bar u, z, \bar z)$. Then $W$ carries a $2 \times 3$ configuration (free $x_0, x_1$ and free $y_0, y_1, y_2$ over $\overline{\mathbb{Q}}$ with all six products $x_iy_j$ in the space) if and only if $\dim_{\overline{\mathbb{Q}}} W = 5$ and $W$ is in one of the following classes:
--
--   - **(P)** $\alpha u^2 + \beta u^3 \in W$ for some $\alpha, \beta \in \overline{\mathbb{Q}}$, not both zero;
--   - **(Q)** $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, u, \bar u, \bar v^2 + ev^2, \beta\bar v^3 + \zeta v^2 + ev^3)$ for some $e, \beta, \zeta \in \overline{\mathbb{Q}}$ with $e\bar e = 1$, $\beta\bar\beta = 1$ and $\zeta = -\beta e^2\bar\zeta$;
--   - **(R)** $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, u, \bar u, g, \bar g)$ with $g = G(v) + \kappa\,\overline{vG(v)}$, for some $\kappa \in \overline{\mathbb{Q}}$ with $\kappa\bar\kappa = 1$ and some $G \in \overline{\mathbb{Q}}[X]$ with $G(0) = 0$ and $\deg G \geq 2$.
--
--   Since $u = sv$ and $\bar u = s/v$, the numbers $z$ are exactly the polynomials in $u$ and $\bar u$ with algebraic coefficients, and $W$ is the conjugation hull of $z$. The three classes are pairwise disjoint (`DiazModulus.laurent_conj_hull_configuration_classes_disjoint`), and each forces $\dim W = 5$ (`DiazModulus.laurent_conj_hull_class_finrank_eq_five`).
--
--   **Proof.** As $s$ is real, $v = u/s$ has $v\bar v = 1$ and $v \notin \overline{\mathbb{Q}}$, and $\mathrm{span}(1, u, \bar u, A, B) = \mathrm{span}(1, v, \bar v, A, B)$ for all $A, B$; this moves every node between $u$ and $v$. Only if: a configuration forces $\dim W > 4$ by `DiazModulus.laurent_conj_hull_finrank_le_four_no_two_by_three_configuration`, and $\dim W \leq 5$ by counting generators; if $W$ contains some $v^2P(v)$ with $P \neq 0$, `DiazModulus.laurent_conj_hull_with_polynomial_part_configuration_class` gives $\alpha v^2 + \beta v^3 \in W$, which is (P) after rescaling by $s^2$ and $s^3$, and otherwise `DiazModulus.laurent_conj_hull_without_polynomial_part_configuration_classes` gives (Q) or (R). If: in class (P), $W$ is conjugation-stable, so it contains the hull of $P(u) = \alpha u^2 + \beta u^3$, which carries a configuration by Theorem C (`DiazModulus.polynomial_hull_two_by_three_configuration_iff`, degree $2$ or $3$). Classes (Q) and (R) carry the configurations of `DiazModulus.laurent_involution_space_carries_two_by_three_configuration` and `DiazModulus.laurent_real_pencil_normal_form_carries_two_by_three_configuration`.
--
--   **Novelty.** Not found in the sources read, and not routine. The "only if" half, the classification, was not found in the sources read; its method is partly that of Bachoc, Serra and Zémor (2017, §7, and Lemma 4). The "if" half consists of printed configurations or substitutions in them: class (P) is Diaz (2007, Th. 7(1)), already in Diaz (2004, Th. 2); class (Q) is Diaz (2004, Th. 2) at $x = (1, (u + \beta\bar u)/s)$; class (R) consists of the real pencil spaces of `DiazModulus.conj_stable_real_pencil_space_carries_two_by_three_configuration`.
-- source:
--   The "only if" half (the classification) was not found in the sources read; the method is partly that of C. Bachoc, O. Serra, G. Zémor, An analogue of Vosper's theorem for extension fields, Math. Proc. Cambridge Philos. Soc. (2017), §7 and Lemma 4. The configurations: class (P), G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Th. 7(1) (p. 390), and already G. Diaz, Utilisation de la conjugaison complexe dans l'étude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Théor. Nombres Bordeaux 16 (2004), 535–553, Th. 2 (p. 538); class (Q), the same Th. 2 (p. 538) at x = (1, (u + βū)/s); class (R), the real pencil spaces of DiazModulus.conj_stable_real_pencil_space_carries_two_by_three_configuration. Uses DiazModulus.laurent_involution_space_carries_two_by_three_configuration, DiazModulus.laurent_real_pencil_normal_form_carries_two_by_three_configuration, DiazModulus.laurent_conj_hull_with_polynomial_part_configuration_class, DiazModulus.laurent_conj_hull_finrank_le_four_no_two_by_three_configuration, DiazModulus.laurent_conj_hull_without_polynomial_part_configuration_classes and DiazModulus.polynomial_hull_two_by_three_configuration_iff. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem laurent_conj_hull_two_by_three_configuration_iff
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hss : s * s = u * conj u)
    (k : ℕ) (c : ℤ → ℂ) (hc : ∀ j, c j ∈ Qbar) :
    (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ)) ↔
      (Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ)) = 5 ∧
      ((∃ α β : ℂ, α ∈ Qbar ∧ β ∈ Qbar ∧ (α ≠ 0 ∨ β ≠ 0) ∧ α * u ^ 2 + β * u ^ 3 ∈ Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ)) ∨
      (∃ e β ζ : ℂ, e ∈ Qbar ∧ β ∈ Qbar ∧ ζ ∈ Qbar ∧ e * conj e = 1 ∧ β * conj β = 1 ∧
        ζ = -(β * e ^ 2 * conj ζ) ∧
        Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) =
          Submodule.span Qbar ({1, u, conj u, conj (u / s) ^ 2 + e * (u / s) ^ 2, β * conj (u / s) ^ 3 + ζ * (u / s) ^ 2 + e * (u / s) ^ 3} : Set ℂ)) ∨
      (∃ κ : ℂ, κ ∈ Qbar ∧ κ * conj κ = 1 ∧ ∃ G : Polynomial ↥Qbar, G.coeff 0 = 0 ∧ 2 ≤ G.natDegree ∧
        Submodule.span Qbar ({1, u, conj u, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * (u / s) ^ j)} : Set ℂ) =
          Submodule.span Qbar ({1, u, conj u, Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G), conj (Polynomial.aeval (u / s) G + κ * conj ((u / s) * Polynomial.aeval (u / s) G))} : Set ℂ)))) := by
  sorry

end DiazModulus
