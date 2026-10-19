-- Prove2me | Theorems.Thm_DiazModulus_rational_degree_one_space_visible_to_four_dimensional_extensions_iff_natDegree_le
-- name    : DiazModulus.rational_degree_one_space_visible_to_four_dimensional_extensions_iff_natDegree_le
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T09:45:10.343587+00:00
-- url     : https://prove2.me/theorems/71a0fb2b-3d61-4ec6-8a95-d5486e5a2a16
-- title:
--   For g = P(u)/Q(u) in lowest terms, span(1, u, ū, g, ug) is visible to the four-dimensional extensions exactly when max(deg P, deg Q) ≤ 2 + [Q(0) = 0]
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $\rho = u\bar u$ algebraic (so $\bar u = \rho/u$). Let $H_0 = \overline{\mathbb{Q}} + \overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u$ and call $W \supseteq H_0$ visible to the four-dimensional extensions if some $w \in W \setminus H_0$ makes $H_0 + \overline{\mathbb{Q}}w$ carry a $2 \times 3$ configuration (free $x_1, x_2$ and free $y_1, y_2, y_3$ over $\overline{\mathbb{Q}}$ with all six products $x_iy_j$ in the space). Let $P, Q \in \overline{\mathbb{Q}}[X]$ be coprime, $g = P(u)/Q(u)$, and suppose $1, u, \bar u, g, ug$ are free over $\overline{\mathbb{Q}}$. Then $W_g = \mathrm{span}_{\overline{\mathbb{Q}}}(1, u, \bar u, g, ug)$ is visible to the four-dimensional extensions if and only if $\max(\deg P, \deg Q) \leq 2 + [Q(0) = 0]$, where $[Q(0) = 0]$ is $1$ if $Q(0) = 0$ and $0$ otherwise.
--
--   **Proof.** $Q \neq 0$, since otherwise $g = 0$. By `DiazModulus.degree_one_space_visible_to_four_dimensional_extensions_iff_cubic_over_quadratic` the space is visible exactly when $u\,R(u)\,P(u)/Q(u) = N(u)$ for such $R, N$; as evaluation at the transcendental $u$ is injective, that is $XRP = NQ$ in $\overline{\mathbb{Q}}[X]$. `DiazModulus.coprime_fraction_cubic_over_quadratic_iff_natDegree_le` turns this into the degree bound.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. Uses DiazModulus.degree_one_space_visible_to_four_dimensional_extensions_iff_cubic_over_quadratic and DiazModulus.coprime_fraction_cubic_over_quadratic_iff_natDegree_le. R17 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem rational_degree_one_space_visible_to_four_dimensional_extensions_iff_natDegree_le
    (u : ℂ) (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u))
    (P Q : (↥Qbar)[X]) (hcop : IsCoprime P Q)
    (hind : LinearIndependent (↥Qbar) ![1, u, conj u, aeval u P / aeval u Q, u * (aeval u P / aeval u Q)]) :
    (∃ w ∈ Submodule.span Qbar ({1, u, conj u, aeval u P / aeval u Q, u * (aeval u P / aeval u Q)} : Set ℂ), w ∉ Submodule.span Qbar ({1, u, conj u} : Set ℂ) ∧
        ∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent (↥Qbar) x ∧ LinearIndependent (↥Qbar) y ∧
          ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, conj u, w} : Set ℂ)) ↔
      max P.natDegree Q.natDegree ≤ 2 + (if Q.coeff 0 = 0 then 1 else 0) := by
  sorry

end DiazModulus
