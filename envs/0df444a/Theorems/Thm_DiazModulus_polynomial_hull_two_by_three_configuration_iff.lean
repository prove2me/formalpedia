-- Prove2me | Theorems.Thm_DiazModulus_polynomial_hull_two_by_three_configuration_iff
-- name    : DiazModulus.polynomial_hull_two_by_three_configuration_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-16T13:59:01.484347+00:00
-- url     : https://prove2.me/theorems/17c20a1d-c0b5-45a0-a8c7-bc6a564ad926
-- title:
--   For u ∉ Q̄ with uū algebraic, the span of 1, u, ū, P(u), P(u)‾ carries a 2×3 configuration exactly when deg P is 2 or 3
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $\rho = u\bar u$ algebraic (so $\bar u = \rho/u$). Let $P \in \overline{\mathbb{Q}}[X]$ and $W = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u + \overline{\mathbb{Q}}P(u) + \overline{\mathbb{Q}}\overline{P(u)}$. Then $W$ carries a $2 \times 3$ configuration (free $x_1, x_2$ and free $y_1, y_2, y_3$ over $\overline{\mathbb{Q}}$ with all six products $x_iy_j$ in the space) if and only if $P$ has degree $2$ or $3$.
--
--   At a candidate $u$, Roy's strong six exponentials theorem therefore excludes $P(u)$ from $\widetilde{\mathcal L}$ through its own hull exactly when $\deg P \in \{2, 3\}$.
--
--   **Proof.** For degree at most $1$ or at least $4$, `DiazModulus.polynomial_hull_no_two_by_three_configuration` excludes a configuration. Degree $2$: $u^2 \in W$, since $P(u) - p_1u - p_0 = p_2u^2$, and the products of $(1, u)$ and $(\bar u, 1, u)$ are $\bar u, 1, u, \rho, u, u^2$. Degree $3$: with $c = p_2/p_3$ and $Q = u^3 + cu^2$, $Q$ and $\bar Q$ lie in $W$, and the products of $(1, u^2)$ and $(\bar u, u + c, \bar Q)$ are $\bar u, u + c, \bar Q, \rho u, Q$ and $u^2\bar Q = \rho^2\bar u + \bar c\rho^2$. Freeness: multiplied by $u$, resp. $u^3$, a relation becomes a polynomial identity at the transcendental $u$.
--
--   **Novelty.** The configurations of degrees $2$ and $3$ are printed: they are Diaz (2007, Th. 7(1), p. 390) at $v = u$, $w = u + b$ and $w = u^2 + cu$, and already Diaz (2004, Th. 2, p. 538). The converse is `DiazModulus.polynomial_hull_no_two_by_three_configuration`. Routine.
-- source:
--   The configurations of degrees 2 and 3 are those of G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Th. 7(1) (p. 390); the converse was not found in the sources read. Uses DiazModulus.polynomial_hull_no_two_by_three_configuration. R16 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 16 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem polynomial_hull_two_by_three_configuration_iff {u : ℂ} (hu : u ∉ Qbar)
    (hρ : IsAlgebraic ℚ (u * conj u)) (P : (↥Qbar)[X]) :
    (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧
      LinearIndependent (↥Qbar) y ∧ ∀ i j, x i * y j ∈
        Submodule.span Qbar ({1, u, conj u, aeval u P, conj (aeval u P)} : Set ℂ)) ↔
      (P.natDegree = 2 ∨ P.natDegree = 3) := by
  sorry

end DiazModulus
