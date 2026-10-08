-- Prove2me | Theorems.Thm_DiazModulus_circle_point_extension_carries_two_by_three_configuration
-- name    : DiazModulus.circle_point_extension_carries_two_by_three_configuration
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-05T07:47:10.883431+00:00
-- url     : https://prove2.me/theorems/dd39ce78-249e-4099-a7ff-76acfc50ff77
-- title:
--   For u ∉ Q̄ with uū algebraic, each space Q̄ + Q̄u + Q̄ū + Q̄w with w = u², ū² or 1/(u − a), a ∈ Q̄ non-zero, carries a 2×3 configuration
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $u\bar u$ algebraic, and let $w$ be $u^2$, $\bar u^2$, or $1/(u - a)$ with $a \in \overline{\mathbb{Q}}$, $a \neq 0$. Then there are $x_1, x_2$, linearly independent over $\overline{\mathbb{Q}}$, and $y_1, y_2, y_3$, linearly independent over $\overline{\mathbb{Q}}$, with all six products $x_i y_j$ in $\overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u + \overline{\mathbb{Q}}w$.
--
--   The configurations are $x = (1, u)$, $y = (u^{-1}, 1, u)$ for $w = u^2$; $x = (1, u^{-1})$, $y = (u, 1, u^{-1})$ for $w = \bar u^2$; and $x = (u^{-1}, (u - a)^{-1})$, $y = (1, u, u^2 - au)$ for $w = 1/(u - a)$. At a candidate $u$, Roy's strong six exponentials theorem turns them into Diaz's exclusions (2007, Cor. 5(1) and 5(4)): none of $u^2$, $\bar u^2$, $1/(u - a)$ lies in $\widetilde{\mathcal{L}}$. The statement itself does not involve $e^u$, so it keeps its content if Diaz's conjecture holds.
--
--   **Proof.** Since $u^{-1} = \bar u/(u\bar u)$ with $u\bar u$ algebraic and non-zero, every product listed lies in the space; for instance $u/(u - a) = 1 + a/(u - a)$ and $(u^2 - au)/(u - a) = u$. Independence comes from the transcendence of $u$ over $\overline{\mathbb{Q}}$: after multiplying by $u$, or by $u(u - a)$, a vanishing combination becomes a polynomial of degree at most $2$ in $u$ with algebraic coefficients, which must be zero; for the last family $a \neq 0$ is used.
--
--   **Novelty.** Not asserted. These are the configurations behind Diaz (2007), Cor. 5(1) and 5(4); the first also appears in `DiazModulus.power_hull_strong_six_exp_configuration_iff`.
-- source:
--   The configurations behind G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Cor. 5(1) and 5(4) (p. 383), used with Roy's strong six exponentials theorem (D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Cor. 2). Formal proof: Diaz modulus mission, 5 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem circle_point_extension_carries_two_by_three_configuration (u w : ℂ) (hu : u ∉ Qbar)
    (hρ : IsAlgebraic ℚ (u * conj u))
    (hw : w = u ^ 2 ∨ w = conj u ^ 2 ∨ ∃ a ∈ Qbar, a ≠ 0 ∧ w = (u - a)⁻¹) :
    ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
      ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ) := by
  sorry

end DiazModulus
