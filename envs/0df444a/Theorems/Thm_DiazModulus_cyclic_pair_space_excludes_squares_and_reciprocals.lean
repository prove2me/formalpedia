-- Prove2me | Theorems.Thm_DiazModulus_cyclic_pair_space_excludes_squares_and_reciprocals
-- name    : DiazModulus.cyclic_pair_space_excludes_squares_and_reciprocals
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-15T11:58:43.314274+00:00
-- url     : https://prove2.me/theorems/bea5ddb7-bcf8-4e0a-91d4-cb4cd4c65a2b
-- title:
--   For u ∉ Q̄ and real algebraic s with s² = uū, the cyclic space with double poles at ±s is five-dimensional and excludes u², ū², 1/(u − e)
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ and let $s \in \overline{\mathbb{Q}}$ be real with $s^2 = u\bar u$ (so $\bar u = s^2/u$). With $v = u/s$, put $G_1 = 1/(v - 1) + 2/(v + 1)$ and $G_2 = 1/(v - 1)^2 + 1/(v - 1) - 2/(v + 1)^2 + 2/(v + 1)$, and let $W$ be the $\overline{\mathbb{Q}}$-span of $1, u, \bar u, G_1, G_2$ (poles at $u = \pm s$, each a double pole). Then the five numbers are free over $\overline{\mathbb{Q}}$, and $W$ contains none of $u^2$, $\bar u^2$ and $1/(u - e)$ for non-zero $e \in \overline{\mathbb{Q}}$.
--
--   **Proof.** As $u \notin \overline{\mathbb{Q}}$, $u \neq \pm s$; and $\bar u u = s^2$, $G_1(u^2 - s^2) = s(3u - s)$, $G_2(u^2 - s^2)^2 = su(3u^2 - 2su + 3s^2)$. For $w = c_1 + c_2u + c_3\bar u + c_4G_1 + c_5G_2$ the product $u(u^2 - s^2)^2w$ is a polynomial of degree $6$ in $u$ over $\overline{\mathbb{Q}}$, with constant term $c_3s^6$, linear coefficient $(c_1 + c_4)s^4$, $u^4$-coefficient $(c_3 - 2c_2)s^2 + 3(c_4 + c_5)s$ and top terms $c_1u^5 + c_2u^6$; as $u$ is transcendental, identities between such polynomials hold coefficientwise. Freeness: $w = 0$ gives $c_2 = c_1 = 0$, then $c_3 = c_4 = 0$ and $3sc_5 = 0$. If $w = u^2$, $u(u^2 - s^2)^2w = u^3(u^2 - s^2)^2$ would have a $u^7$ term. If $w = \bar u^2 = s^4/u^2$, then $u \cdot u(u^2 - s^2)^2w = s^4(u^2 - s^2)^2$ would have the constant term $s^8$, which $u$ times a polynomial cannot have. For $(u - e)^{-1}$, $(u - e)\,u(u^2 - s^2)^2w = u(u^2 - s^2)^2$ evaluated at $e$ gives $e(e^2 - s^2)^2 = 0$, so $e = \pm s$; then explicit combinations of the coefficient equations give $8s^5 = 0$, resp. $4s^5 = 0$. In terms of poles: an element of $W$ with a pole at $s$ has one at $-s$, and conversely.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. R15 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 15 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem cyclic_pair_space_excludes_squares_and_reciprocals
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u) :
    LinearIndependent (↥Qbar) ![1, u, conj u, (s / (u - s) + 2 * s / (u + s)), (s * s / (u - s) ^ 2 + s / (u - s) - 2 * (s * s) / (u + s) ^ 2 + 2 * s / (u + s))] ∧
      u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, (s / (u - s) + 2 * s / (u + s)), (s * s / (u - s) ^ 2 + s / (u - s) - 2 * (s * s) / (u + s) ^ 2 + 2 * s / (u + s))} : Set ℂ) ∧
      conj u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, (s / (u - s) + 2 * s / (u + s)), (s * s / (u - s) ^ 2 + s / (u - s) - 2 * (s * s) / (u + s) ^ 2 + 2 * s / (u + s))} : Set ℂ) ∧
      ∀ e ∈ Qbar, e ≠ 0 → (u - e)⁻¹ ∉ Submodule.span Qbar ({1, u, conj u, (s / (u - s) + 2 * s / (u + s)), (s * s / (u - s) ^ 2 + s / (u - s) - 2 * (s * s) / (u + s) ^ 2 + 2 * s / (u + s))} : Set ℂ) := by
  sorry

end DiazModulus
