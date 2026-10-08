-- Prove2me | Theorems.Thm_DiazModulus_circle_point_extension_two_by_three_configuration_iff
-- name    : DiazModulus.circle_point_extension_two_by_three_configuration_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-05T07:47:29.838388+00:00
-- url     : https://prove2.me/theorems/f2c817ff-c9ef-49ae-94c0-78ef031172be
-- title:
--   For u ∉ Q̄ with uū algebraic and z ∉ Q̄ + Q̄u + Q̄ū, the space Q̄ + Q̄u + Q̄ū + Q̄z carries a 2×3 configuration exactly when z ∈ Q̄ + Q̄u + Q̄ū + Q̄w for w = u², ū² or 1/(u − a), a ∈ Q̄ non-zero
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $u\bar u$ algebraic, put $H_0 = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$, and let $z \notin H_0$. There are $x_1, x_2$, linearly independent over $\overline{\mathbb{Q}}$, and $y_1, y_2, y_3$, linearly independent over $\overline{\mathbb{Q}}$, with all six products $x_i y_j$ in $H_0 + \overline{\mathbb{Q}}z$ if and only if
--   $$z \in H_0 + \overline{\mathbb{Q}}\,w \quad\text{for some } w \in \{u^2, \bar u^2\} \cup \{1/(u - a) : a \in \overline{\mathbb{Q}},\ a \neq 0\}.$$
--
--   This classifies the four-dimensional extensions of $H_0$ that carry a configuration of Roy's strong six exponentials theorem. A candidate for Diaz's conjecture satisfies the hypotheses ($u \notin \overline{\mathbb{Q}}$ by Hermite–Lindemann), but the statement does not involve $e^u$, so it keeps its content if Diaz's conjecture holds. Since $\widetilde{\mathcal{L}}$ is closed under complex conjugation, a hypothesis $z \in \widetilde{\mathcal{L}}$ also brings $\bar z$; the five-dimensional spaces $H_0 + \overline{\mathbb{Q}}z + \overline{\mathbb{Q}}\bar z$ are not covered.
--
--   **Proof.** If $z \in H_0 + \overline{\mathbb{Q}}w$, then $w \in H_0 + \overline{\mathbb{Q}}z$ because $z \notin H_0$, and the configuration of `DiazModulus.circle_point_extension_carries_two_by_three_configuration` lies in $H_0 + \overline{\mathbb{Q}}z$. Conversely, `DiazModulus.two_by_three_configuration_forces_progression` writes $V = H_0 + \overline{\mathbb{Q}}z$ as $\beta(\overline{\mathbb{Q}} + \overline{\mathbb{Q}}h + \overline{\mathbb{Q}}h^2 + \overline{\mathbb{Q}}h^3)$ with $h \notin \overline{\mathbb{Q}}$, and `DiazModulus.circle_hull_progression_contains_square_or_reciprocal` puts in this progression, which contains $1, u, \bar u$, one of $w = u^2$, $w = \bar u^2$ and $w = 1/(u - \alpha)$ with $\alpha$ algebraic and non-zero. Such a $w$ is not in $H_0$: clearing denominators would make $u$ a root of a non-zero polynomial of degree at most $3$ over $\overline{\mathbb{Q}}$. As $w \in H_0 + \overline{\mathbb{Q}}z$ and $w \notin H_0$, exchange gives $z \in H_0 + \overline{\mathbb{Q}}w$.
--
--   **Novelty.** The classification was not found in the sources read. With Roy's strong six exponentials theorem, its "if" direction gives at a candidate the exclusions of Diaz (2007, Cor. 5(1) and 5(4)); every configuration has the shape of Fischler (2001, Lemma 6.1) and Diaz (2007, Th. 7(2)).
-- source:
--   The classification was not found in the sources read. With the strong six exponentials theorem (D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Cor. 2), the "if" direction gives at a candidate the exclusions of G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Cor. 5(1) and 5(4) (p. 383); every configuration has the shape of S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Lemma 6.1 (p. 184), and of Diaz's Th. 7(2) (p. 390). Formal proof: Diaz modulus mission, 5 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem circle_point_extension_two_by_three_configuration_iff (u z : ℂ) (hu : u ∉ Qbar)
    (hρ : IsAlgebraic ℚ (u * conj u))
    (hz : z ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ)) :
    (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
        ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, z} : Set ℂ)) ↔
      (z ∈ Submodule.span Qbar ({1, u, conj u, u ^ 2} : Set ℂ) ∨
        z ∈ Submodule.span Qbar ({1, u, conj u, conj u ^ 2} : Set ℂ) ∨
        ∃ a ∈ Qbar, a ≠ 0 ∧ z ∈ Submodule.span Qbar ({1, u, conj u, (u - a)⁻¹} : Set ℂ)) := by
  sorry

end DiazModulus
