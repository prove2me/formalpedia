-- Prove2me | Theorems.Thm_DiazModulus_laurent_cubic_space_excludes_squares_and_reciprocals
-- name    : DiazModulus.laurent_cubic_space_excludes_squares_and_reciprocals
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-14T07:30:11.737298+00:00
-- url     : https://prove2.me/theorems/ba964399-75db-4df3-b4d8-a98ddf919fe7
-- title:
--   For u ∉ Q̄ and real algebraic s with s² = uū, the span of 1, u, ū, u³/s³ + u²/s², ū³/s³ + ū²/s² is five-dimensional and contains none of u², ū², 1/(u − b)
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ and let $s \in \overline{\mathbb{Q}}$ be real with $s^2 = u\bar u$ (so $\bar u = s^2/u$; with $v = u/s$, conjugation acts as $v \mapsto 1/v$ on coefficients). Put $F = u^3/s^3 + u^2/s^2$ and let $W_1$ be the $\overline{\mathbb{Q}}$-span of $1, u, \bar u, F, \bar F$ (in $v$: $v^{-1}, 1, v, v^3 + v^2, v^{-3} + v^{-2}$). Then the five numbers are free over $\overline{\mathbb{Q}}$, and $W_1$ contains none of $u^2$, $\bar u^2$ and $1/(u - b)$ for non-zero $b \in \overline{\mathbb{Q}}$.
--
--   **Proof.** From $\bar u u = s^2$, $s^3F = u^3 + su^2$ and $u^3\bar F = s^3 + s^2u$, the number $s^3u^3w$ for $w = c_1 + c_2u + c_3\bar u + c_4F + c_5\bar F$ is a polynomial of degree $6$ in $u$ with coefficients $c_5s^6, c_5s^5, c_3s^5, c_1s^3, c_2s^3, c_4s, c_4$; as $u$ is transcendental, every coefficient of a vanishing combination is zero. So the five numbers are free; $u^2 \notin W_1$ because the $u^5$ and $u^6$ coefficients are tied, and $\bar u^2 = s^4/u^2 \notin W_1$ because the $u^0$ and $u^1$ coefficients are; for $1/(u - b)$, the cleared identity $(X - b)L(X) = s^3X^3$ at $X = b$ gives $s^3b^3 = 0$.
--
--   **Novelty.** Not found in the sources read; it is short.
-- source:
--   Not found in the sources read. R14 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 14 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem laurent_cubic_space_excludes_squares_and_reciprocals
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u) :
    LinearIndependent (↥Qbar) ![1, u, conj u, (u ^ 3 / (s * s * s) + u ^ 2 / (s * s)), (conj u ^ 3 / (s * s * s) + conj u ^ 2 / (s * s))] ∧
      u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, (u ^ 3 / (s * s * s) + u ^ 2 / (s * s)), (conj u ^ 3 / (s * s * s) + conj u ^ 2 / (s * s))} : Set ℂ) ∧
      conj u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, (u ^ 3 / (s * s * s) + u ^ 2 / (s * s)), (conj u ^ 3 / (s * s * s) + conj u ^ 2 / (s * s))} : Set ℂ) ∧
      ∀ b ∈ Qbar, b ≠ 0 → (u - b)⁻¹ ∉ Submodule.span Qbar ({1, u, conj u, (u ^ 3 / (s * s * s) + u ^ 2 / (s * s)), (conj u ^ 3 / (s * s * s) + conj u ^ 2 / (s * s))} : Set ℂ) := by
  sorry

end DiazModulus
