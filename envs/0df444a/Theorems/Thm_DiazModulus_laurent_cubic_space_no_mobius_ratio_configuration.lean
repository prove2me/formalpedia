-- Prove2me | Theorems.Thm_DiazModulus_laurent_cubic_space_no_mobius_ratio_configuration
-- name    : DiazModulus.laurent_cubic_space_no_mobius_ratio_configuration
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-14T07:30:16.824612+00:00
-- url     : https://prove2.me/theorems/83ef8e17-9cee-499c-871e-9c3bf39f1396
-- title:
--   For u ∉ Q̄ and real algebraic s with s² = uū, the span of 1, u, ū, u³/s³ + u²/s², ū³/s³ + ū²/s² carries no 2×3 configuration whose ratio x₂/x₁ is a Möbius function of u
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ and let $s \in \overline{\mathbb{Q}}$ be real with $s^2 = u\bar u$ (so $\bar u = s^2/u$; with $v = u/s$, conjugation acts as $v \mapsto 1/v$ on coefficients). Put $F = u^3/s^3 + u^2/s^2$ and let $W_1$ be the $\overline{\mathbb{Q}}$-span of $1, u, \bar u, F, \bar F$ (in $v$: $v^{-1}, 1, v, v^3 + v^2, v^{-3} + v^{-2}$). Then there are no free $x_1, x_2$ and free $y_1, y_2, y_3$ with all six products in $W_1$ and $x_2/x_1 = (\alpha u + \beta)/(\gamma u + \delta)$, $\alpha, \beta, \gamma, \delta \in \overline{\mathbb{Q}}$, $\alpha\delta - \beta\gamma \neq 0$.
--
--   $W_1$ answers a question left open in R10: a conjugation-stable five-dimensional space containing $H_0 = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$ can carry a configuration that Theorem B does not see without having a configuration factor of degree one, so it is not one of R11's real pencil spaces. Every real pencil space has a configuration of degree one (`DiazModulus.conj_stable_real_pencil_space_carries_two_by_three_configuration`), so $W_1$ is none of them.
--
--   **Proof.** Suppose $x_1(\gamma u + \delta) = x_0(\alpha u + \beta)$ and all $x_iy_j \in W_1$. Put $c = \alpha x_0 - \gamma x_1$, non-zero because $x$ is free and $\alpha\delta - \beta\gamma \neq 0$. Then $t_j = cy_j = \alpha x_0y_j - \gamma x_1y_j \in W_1$ and $ut_j = \delta x_1y_j - \beta x_0y_j \in W_1$. But $t, ut \in W_1$ forces $t \in \overline{\mathbb{Q}} + \overline{\mathbb{Q}}\bar u$ (comparing the coefficients of $u\cdot s^3u^3t = s^3u^3\cdot ut$, a polynomial identity of degree $7$), and the three free $t_j$ cannot lie in a two-dimensional space.
--
--   **Novelty.** Not found in the sources read; it is short.
-- source:
--   Not found in the sources read. R14 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 14 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem laurent_cubic_space_no_mobius_ratio_configuration
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u) :
    ¬ ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (α β γ δ : ℂ), α ∈ Qbar ∧ β ∈ Qbar ∧ γ ∈ Qbar ∧ δ ∈ Qbar ∧
      α * δ - β * γ ≠ 0 ∧ LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      (∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, (u ^ 3 / (s * s * s) + u ^ 2 / (s * s)), (conj u ^ 3 / (s * s * s) + conj u ^ 2 / (s * s))} : Set ℂ)) ∧ x 1 * (γ * u + δ) = x 0 * (α * u + β) := by
  sorry

end DiazModulus
