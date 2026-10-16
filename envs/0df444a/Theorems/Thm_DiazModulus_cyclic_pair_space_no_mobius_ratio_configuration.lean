-- Prove2me | Theorems.Thm_DiazModulus_cyclic_pair_space_no_mobius_ratio_configuration
-- name    : DiazModulus.cyclic_pair_space_no_mobius_ratio_configuration
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-15T11:58:46.212732+00:00
-- url     : https://prove2.me/theorems/dfc3244d-f7c4-4044-affb-de9419ac2e1c
-- title:
--   For u ∉ Q̄ and real algebraic s with s² = uū, the cyclic space with double poles at ±s carries no 2×3 configuration whose ratio is a Möbius function of u
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ and let $s \in \overline{\mathbb{Q}}$ be real with $s^2 = u\bar u$ (so $\bar u = s^2/u$). With $v = u/s$, put $G_1 = 1/(v - 1) + 2/(v + 1)$ and $G_2 = 1/(v - 1)^2 + 1/(v - 1) - 2/(v + 1)^2 + 2/(v + 1)$, and let $W$ be the $\overline{\mathbb{Q}}$-span of $1, u, \bar u, G_1, G_2$ (poles at $u = \pm s$, each a double pole). Then there are no free $x_1, x_2$ and free $y_1, y_2, y_3$ with all six products in $W$ and $x_2/x_1 = (\alpha u + \beta)/(\gamma u + \delta)$, $\alpha, \beta, \gamma, \delta \in \overline{\mathbb{Q}}$, $\alpha\delta - \beta\gamma \neq 0$.
--
--   So, like R14's $W_1$, it is none of R11's real pencil spaces.
--
--   **Proof.** First, if $t$ and $ut$ both lie in $W$, then $t \in \overline{\mathbb{Q}} + \overline{\mathbb{Q}}\bar u$. Write $t = c_1 + c_2u + c_3\bar u + c_4G_1 + c_5G_2$, and $ut$ likewise, and multiply each by $u(u^2 - s^2)^2$, which turns them into polynomials of degree $6$ in $u$ (as in `DiazModulus.cyclic_pair_space_excludes_squares_and_reciprocals`). Then $u \cdot u(u^2 - s^2)^2t = u(u^2 - s^2)^2 \cdot ut$ is an identity of degree $7$ over $\overline{\mathbb{Q}}$ at the transcendental $u$. Its $u^7$ coefficient gives $c_2 = 0$, and two combinations of the eight coefficient equations give $16s^6c_4 = 0$ and $16s^6c_5 = 0$. (In terms of poles: in $W$ the leading polar coefficients at $s$ and $-s$ are in the ratio $1 : -2$ for double poles and $1 : 2$ for simple ones, and multiplication by $u$ changes the sign of that ratio.) Now let free $x$ and $y$ have $x_iy_j \in W$ and $x_2(\gamma u + \delta) = x_1(\alpha u + \beta)$ with $\alpha\delta - \beta\gamma \neq 0$. Then $c = \alpha x_1 - \gamma x_2 \neq 0$ by the freeness of $x$, the three numbers $t_j = cy_j$ are free and lie in $W$, and $ut_j = \delta x_2y_j - \beta x_1y_j \in W$. So three free numbers lie in the two-dimensional $\overline{\mathbb{Q}} + \overline{\mathbb{Q}}\bar u$, which is impossible.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. R15 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 15 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem cyclic_pair_space_no_mobius_ratio_configuration
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u) :
    ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (α β γ δ : ℂ), α ∈ Qbar ∧ β ∈ Qbar ∧ γ ∈ Qbar ∧ δ ∈ Qbar ∧
      α * δ - β * γ ≠ 0 ∧ LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      (∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, (s / (u - s) + 2 * s / (u + s)), (s * s / (u - s) ^ 2 + s / (u - s) - 2 * (s * s) / (u + s) ^ 2 + 2 * s / (u + s))} : Set ℂ)) ∧ x 1 * (γ * u + δ) = x 0 * (α * u + β) := by
  sorry

end DiazModulus
