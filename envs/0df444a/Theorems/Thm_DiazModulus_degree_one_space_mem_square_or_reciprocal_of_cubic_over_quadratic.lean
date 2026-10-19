-- Prove2me | Theorems.Thm_DiazModulus_degree_one_space_mem_square_or_reciprocal_of_cubic_over_quadratic
-- name    : DiazModulus.degree_one_space_mem_square_or_reciprocal_of_cubic_over_quadratic
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T09:45:12.605935+00:00
-- url     : https://prove2.me/theorems/3e585daf-cd25-4a89-9ca4-22937d777548
-- title:
--   If 1, u, ū, g, ug are free and u·R(u)·g = N(u) with R ≠ 0, deg R ≤ 2, deg N ≤ 3, their span contains u², ū² or some 1/(u − a)
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $\rho = u\bar u$ algebraic (so $\bar u = \rho/u$). Let $g \in \mathbb{C}$ with $1, u, \bar u, g, ug$ free over $\overline{\mathbb{Q}}$, and suppose $u\,R(u)\,g = N(u)$ for some $R, N \in \overline{\mathbb{Q}}[X]$ with $R \neq 0$, $\deg R \leq 2$ and $\deg N \leq 3$. Then $W_g = \mathrm{span}_{\overline{\mathbb{Q}}}(1, u, \bar u, g, ug)$ contains $u^2$, $\bar u^2$ or some $1/(u - a)$ with $a \in \overline{\mathbb{Q}}^\times$.
--
--   **Proof.** Put $D = uR(u) \neq 0$ and $\varphi(M) = M(u)/D$, a $\overline{\mathbb{Q}}$-linear map on $\overline{\mathbb{Q}}[X]$. The generators $1, u, \bar u, g, ug$ are $\varphi(XR), \varphi(X^2R), \varphi(\rho R), \varphi(N), \varphi(XN)$, all of degree at most $4$, so $W_g$ lies in the image of the polynomials of degree below $5$, of dimension at most $5$. As $\dim W_g = 5$, the two are equal. If $\deg R \leq 1$ then $u^2 = \varphi(X^3R)$; if $R(0) = 0$, $R = XR_1$ and $\bar u^2 = \varphi(\rho^2R_1)$; otherwise $R$ has a root $b \in \overline{\mathbb{Q}}^\times$, $R = (X - b)R_1$ and $1/(u - b) = \varphi(XR_1)$.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. R17 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem degree_one_space_mem_square_or_reciprocal_of_cubic_over_quadratic
    (u g : ℂ) (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u))
    (hind : LinearIndependent (↥Qbar) ![1, u, conj u, g, u * g])
    (R N : (↥Qbar)[X]) (hR : R ≠ 0) (hRd : R.natDegree ≤ 2) (hNd : N.natDegree ≤ 3)
    (hRN : u * aeval u R * g = aeval u N) :
    u ^ 2 ∈ Submodule.span Qbar ({1, u, conj u, g, u * g} : Set ℂ) ∨
      conj u ^ 2 ∈ Submodule.span Qbar ({1, u, conj u, g, u * g} : Set ℂ) ∨
      ∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ Submodule.span Qbar ({1, u, conj u, g, u * g} : Set ℂ) := by
  sorry

end DiazModulus
