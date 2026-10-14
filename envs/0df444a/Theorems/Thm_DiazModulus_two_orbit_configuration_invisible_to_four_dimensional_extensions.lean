-- Prove2me | Theorems.Thm_DiazModulus_two_orbit_configuration_invisible_to_four_dimensional_extensions
-- name    : DiazModulus.two_orbit_configuration_invisible_to_four_dimensional_extensions
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-14T07:30:33.641983+00:00
-- url     : https://prove2.me/theorems/41926461-6ec2-4a66-be33-2dddce6c8db1
-- title:
--   For u ∉ Q̄ with uū algebraic and the two-orbit space of a, b, α, β, γ, δ with α ≠ β or γ ≠ δ: a spanning 2×3 configuration that no Q̄ + Q̄u + Q̄ū + Q̄w inside it carries
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$, let $a, b \in \overline{\mathbb{Q}}^\times$ with $a^2 \neq b^2$ and $\alpha, \beta, \gamma, \delta \in \overline{\mathbb{Q}}^\times$, put $g_1 = \alpha/(u - a) + \beta/(u + a)$, $g_2 = \gamma/(u - b) + \delta/(u + b)$, and let $W$ be the $\overline{\mathbb{Q}}$-span of $1, u, u^{-1}, g_1, g_2$. Suppose $\alpha \neq \beta$ or $\gamma \neq \delta$, and that $u\bar u$ is algebraic; put $H_0 = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$. Then the six products of $(1, u^2)$ and $(u^{-1}, g_1, g_2)$ lie in $W$ and span it, and for no $w \in W$ outside $H_0$ does $H_0 + \overline{\mathbb{Q}}w$ carry a configuration.
--
--   For $\alpha = \beta$, $\gamma = \delta$ the space is R7's two-pole family, whose configuration is a progression; here the products span the whole space.
--
--   **Proof.** With $x = (1, u^2)$ and $y = (u^{-1}, g_1, g_2)$: $u^2/(u \mp a) = u \pm a + a^2/(u \mp a)$ gives $u^2g_1 = (\alpha+\beta)u + (\alpha-\beta)a + a^2g_1$, and likewise for $g_2$, so the six products lie in $W$; their span contains $1$ because $(\alpha-\beta)a$ or $(\gamma-\delta)b$ is non-zero, hence equals $W$. $x$ is free since $u^2 \notin \overline{\mathbb{Q}}$, and $y$ by `DiazModulus.two_orbit_space_excludes_squares_and_reciprocals`. Since $\bar u = \rho u^{-1}$, every $H_0 + \overline{\mathbb{Q}}w$ with $w \in W$ lies in $W$, and Theorem B (`DiazModulus.circle_point_extension_two_by_three_configuration_iff`) with exchange would put $u^2$, $\bar u^2$ (so $u^{-2}$) or some $1/(u - e)$ in $W$, which the same node excludes.
--
--   **Novelty.** Not found in the sources read; it is short.
-- source:
--   Not found in the sources read. Uses DiazModulus.circle_point_extension_two_by_three_configuration_iff (Theorem B of the Diaz modulus mission). R14 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 14 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem two_orbit_configuration_invisible_to_four_dimensional_extensions
    (u : ℂ) (hu : u ∉ Qbar) (a b α β γ δ : ℂ) (ha : a ∈ Qbar) (hb : b ∈ Qbar) (hα : α ∈ Qbar) (hβ : β ∈ Qbar)
    (hγ : γ ∈ Qbar) (hδ : δ ∈ Qbar) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ^ 2 ≠ b ^ 2)
    (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (hγ0 : γ ≠ 0) (hδ0 : δ ≠ 0)
    (hαγ : α ≠ β ∨ γ ≠ δ) (hρ : IsAlgebraic ℚ (u * conj u)) :
    (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
        (∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, u⁻¹, (α / (u - a) + β / (u + a)), (γ / (u - b) + δ / (u + b))} : Set ℂ)) ∧
        Submodule.span Qbar (Set.range (fun p : Fin 2 × Fin 3 => x p.1 * y p.2)) = Submodule.span Qbar ({1, u, u⁻¹, (α / (u - a) + β / (u + a)), (γ / (u - b) + δ / (u + b))} : Set ℂ)) ∧
      ∀ w ∈ Submodule.span Qbar ({1, u, u⁻¹, (α / (u - a) + β / (u + a)), (γ / (u - b) + δ / (u + b))} : Set ℂ), w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) →
        ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
  sorry

end DiazModulus
