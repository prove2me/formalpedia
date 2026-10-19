-- Prove2me | Theorems.Thm_DiazModulus_real_polynomial_hull_no_two_by_three_configuration
-- name    : DiazModulus.real_polynomial_hull_no_two_by_three_configuration
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-16T13:59:12.904963+00:00
-- url     : https://prove2.me/theorems/5522d7c1-37d5-462c-bbb4-10356969dc24
-- title:
--   For u ∉ Q̄ with uū algebraic and G a real polynomial with algebraic coefficients, z = G(Re u, Im u) has no 2×3 configuration in its hull
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $\rho = u\bar u$ algebraic (so $\bar u = \rho/u$). Let $G \in \mathbb{R}[a, b]$ have algebraic coefficients and $z = G(\mathrm{Re}\,u, \mathrm{Im}\,u)$. Then $\overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u + \overline{\mathbb{Q}}z + \overline{\mathbb{Q}}\bar z$ carries no $2 \times 3$ configuration (free $x_1, x_2$ and free $y_1, y_2, y_3$ over $\overline{\mathbb{Q}}$ with all six products $x_iy_j$ in the space).
--
--   So at a candidate, Roy's theorem cannot exclude such a $z$, for example $(\mathrm{Re}\,u)^2$ or $\mathrm{Re}\,u \cdot \mathrm{Im}\,u$, from $\widetilde{\mathcal L}$ through its own hull.
--
--   **Proof.** $z$ is real, so the span is $H_0 + \overline{\mathbb{Q}}z$ with $H_0 = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$. Since $\mathrm{Re}\,u = (u + \bar u)/2$, $\mathrm{Im}\,u = (u - \bar u)/(2i)$ and $\bar u = \rho/u$, $u^Nz = R(u)$ for some $R \in \overline{\mathbb{Q}}[X]$. For a real $w$ of this kind outside $H_0$, Theorem B puts $w$ in $H_0 + \overline{\mathbb{Q}}t$ with $t = u^2$, $\bar u^2$ or $(u - \alpha)^{-1}$: if $w \equiv cu^2$, conjugating gives $cu^2 - \bar c\bar u^2 \in H_0$, so $c = 0$ ($u$ is transcendental); $\bar u^2$ is symmetric; and $(u - \alpha)^{-1}$ is excluded by evaluating at $\alpha$ the polynomial identity obtained after multiplying by $u^{N+1}(u - \alpha)$. So no such $w$ carries a configuration. If $z \notin H_0$ take $w = z$; if $z \in H_0$, the span is $H_0 \subseteq H_0 + \overline{\mathbb{Q}}(u^2 + \bar u^2)$, and $w = u^2 + \bar u^2$ applies.
--
--   **Novelty.** Not found in the sources read; routine, as a consequence of Theorem B (`DiazModulus.circle_point_extension_two_by_three_configuration_iff`).
-- source:
--   Not found in the sources read. Uses DiazModulus.circle_point_extension_two_by_three_configuration_iff. R16 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 16 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem real_polynomial_hull_no_two_by_three_configuration {u : ℂ} (hu : u ∉ Qbar)
    (hρ : IsAlgebraic ℚ (u * conj u)) (G : MvPolynomial (Fin 2) ℝ)
    (hG : ∀ s, IsAlgebraic ℚ ((G.coeff s : ℝ) : ℂ)) :
    ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
      LinearIndependent (↥Qbar) y ∧ ∀ i j, x i * y j ∈
        Submodule.span Qbar ({1, u, conj u, ((MvPolynomial.eval ![u.re, u.im] G : ℝ) : ℂ),
          conj ((MvPolynomial.eval ![u.re, u.im] G : ℝ) : ℂ)} : Set ℂ) := by
  sorry

end DiazModulus
