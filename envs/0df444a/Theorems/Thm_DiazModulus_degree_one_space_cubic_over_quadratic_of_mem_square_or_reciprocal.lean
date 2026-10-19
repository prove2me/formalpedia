-- Prove2me | Theorems.Thm_DiazModulus_degree_one_space_cubic_over_quadratic_of_mem_square_or_reciprocal
-- name    : DiazModulus.degree_one_space_cubic_over_quadratic_of_mem_square_or_reciprocal
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T09:45:01.481717+00:00
-- url     : https://prove2.me/theorems/068f43ed-72e8-4dc9-923c-0826ccb40c16
-- title:
--   If span(1, u, ū, g, ug) contains u², ū² or some 1/(u − a), then u·R(u)·g = N(u) with R ≠ 0, deg R ≤ 2, deg N ≤ 3
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $\rho = u\bar u$ algebraic (so $\bar u = \rho/u$). Let $g \in \mathbb{C}$ and $W_g = \mathrm{span}_{\overline{\mathbb{Q}}}(1, u, \bar u, g, ug)$. If $W_g$ contains $u^2$, $\bar u^2$ or some $1/(u - a)$ with $a \in \overline{\mathbb{Q}}^\times$, then $u\,R(u)\,g = N(u)$ for some $R, N \in \overline{\mathbb{Q}}[X]$ with $R \neq 0$, $\deg R \leq 2$ and $\deg N \leq 3$.
--
--   **Proof.** Write the element as $t = c_0 + c_1u + c_2\bar u + \alpha g + \beta ug$, replace $\bar u$ by $\rho/u$ and clear denominators. For $t = u^2$ take $R = \alpha + \beta X$, $N = X^3 - c_1X^2 - c_0X - c_2\rho$; for $t = \bar u^2$, $R = X(\alpha + \beta X)$, $N = \rho^2 - X(c_0X + c_1X^2 + c_2\rho)$; for $t = 1/(u - a)$, $R = (X - a)(\alpha + \beta X)$, $N = X - (X - a)(c_0X + c_1X^2 + c_2\rho)$. In each case $N \neq 0$ (monic, $N(0) = \rho^2$, $N(a) = a$), so $R \neq 0$: otherwise $N(u) = 0$, while $u$ is transcendental over $\overline{\mathbb{Q}}$.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. R17 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem degree_one_space_cubic_over_quadratic_of_mem_square_or_reciprocal
    (u g : ℂ) (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u))
    (ht : u ^ 2 ∈ Submodule.span Qbar ({1, u, conj u, g, u * g} : Set ℂ) ∨
        conj u ^ 2 ∈ Submodule.span Qbar ({1, u, conj u, g, u * g} : Set ℂ) ∨
        ∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ Submodule.span Qbar ({1, u, conj u, g, u * g} : Set ℂ)) :
    ∃ R N : (↥Qbar)[X], R ≠ 0 ∧ R.natDegree ≤ 2 ∧ N.natDegree ≤ 3 ∧ u * aeval u R * g = aeval u N := by
  sorry

end DiazModulus
