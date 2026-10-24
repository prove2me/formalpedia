-- Prove2me | Theorems.Thm_DiazModulus_conj_hull_finrank_four_two_by_three_configuration_iff
-- name    : DiazModulus.conj_hull_finrank_four_two_by_three_configuration_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-23T07:19:16.419398+00:00
-- url     : https://prove2.me/theorems/1911bedb-1afb-4db1-be0b-a943e00c12ef
-- title:
--   A four-dimensional conjugation hull of any z carries a 2×3 configuration iff z ∈ span(1, u, ū, 1/(u − a)) with aā = |u|²
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Suppose $u\bar u$ is algebraic, let $z \in \mathbb{C}$ be arbitrary, and suppose the conjugation hull $W_z = \mathrm{span}(1, u, \bar u, z, \bar z)$ has dimension $4$. Then $W_z$ carries a $2 \times 3$ configuration (linearly independent $x_0, x_1 \in \mathbb{C}$ and linearly independent $y_0, y_1, y_2 \in \mathbb{C}$ with every $x_iy_j \in W_z$) if and only if there is $a \in \overline{\mathbb{Q}}$ with $a\bar a = u\bar u$ and $z \in \mathrm{span}(1, u, \bar u, (u - a)^{-1})$.
--
--   When this holds, $W_z = \mathrm{span}(1, u, \bar u, (u - a)^{-1})$, with $a$ on the circle $|a| = |u|$.
--
--   **Proof.** Put $\rho = u\bar u$, $H = \mathrm{span}(1, u, \bar u)$ and $V = H + \overline{\mathbb{Q}} z$. The family $1, u, \bar u$ is independent (a relation times $u$ is a polynomial of degree at most $2$ vanishing at $u$). So $z \notin H$, since otherwise $\bar z \in H$ and $W_z \subseteq H$ would have dimension at most $3$; and $\bar z \in V$, since otherwise $\bar z, z, 1, u, \bar u$ would be independent. So $W_z = V$, and Theorem B (`DiazModulus.circle_point_extension_two_by_three_configuration_iff`) applies to $V$. ($\Leftarrow$) $a\bar a = \rho \neq 0$ gives $a \neq 0$, and Theorem B's third alternative puts a configuration in $V = W_z$. ($\Rightarrow$) Theorem B gives $z \in H + \overline{\mathbb{Q}} w$ with $w = u^2$, $\bar u^2$ or $(u - a)^{-1}$, $a \in \overline{\mathbb{Q}} \setminus \{0\}$. By exchange $w \in V$, and $W_z$ is conjugation-stable, so $\bar w \in W_z = V \subseteq H + \overline{\mathbb{Q}} w$. For $w = u^2$ this puts $\bar u^2 = \rho^2u^{-2}$ in $H + \overline{\mathbb{Q}} u^2$, for $w = \bar u^2$ it puts $u^2$ in $H + \overline{\mathbb{Q}}\bar u^2$; clearing denominators, $u$ would be a root of a non-zero polynomial over $\overline{\mathbb{Q}}$. For $w = (u - a)^{-1}$, with $b = \rho/\bar a$, $(u - b)^{-1}$ is a combination of $1$ and $\bar w$, so it lies in $H + \overline{\mathbb{Q}}(u - a)^{-1}$; multiplying out by $u(u - a)(u - b)$ and evaluating at $b$ gives $b(b - a) = 0$, so $b = a$, that is, $a\bar a = \rho$.
--
--   **Novelty.** Theorem B (`DiazModulus.circle_point_extension_two_by_three_configuration_iff`, 10.6) plus conjugation-stability; routine. The configuration is printed: rescaled, it is Diaz's Théorème 7(1) (2007) at $v = 1/(u - a)$, and at a candidate the exclusion of $1/(u - a)$ is his Corollaire 5(4).
-- source:
--   Theorem B (DiazModulus.circle_point_extension_two_by_three_configuration_iff, 10.6) combined with the conjugation-stability of the hull. The configuration is, after rescaling, G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Théorème 7(1) at v = 1/(u − a); at a candidate the exclusion is its Corollaire 5(4). Uses DiazModulus.circle_point_extension_two_by_three_configuration_iff. R20 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 23 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem conj_hull_finrank_four_two_by_three_configuration_iff (u z : ℂ) (hu : u ∉ Qbar)
    (hρ : IsAlgebraic ℚ (u * conj u))
    (h4 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ)) = 4) :
    (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
        ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ)) ↔
    ∃ a ∈ Qbar, a * conj a = u * conj u ∧
      z ∈ Submodule.span Qbar ({1, u, conj u, (u - a)⁻¹} : Set ℂ) := by
  sorry

end DiazModulus
