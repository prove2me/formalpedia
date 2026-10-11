-- Prove2me | Theorems.Thm_DiazModulus_real_pencil_quartic_space_excludes_squares_and_reciprocals
-- name    : DiazModulus.real_pencil_quartic_space_excludes_squares_and_reciprocals
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-11T08:03:27.885969+00:00
-- url     : https://prove2.me/theorems/19f4aca0-9d73-4c13-b43c-d9f02199b074
-- title:
--   For u ∉ Q̄ and real algebraic s with s² = uū, with f = u²/s² + s²/u²: 1, u, ū, f, f/(s + u) are free and their span contains none of u², ū², 1/(u − b)
-- statement:
--   Let $u \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ and let $s \in \overline{\mathbb{Q}}$ be real with $s^2 = u\bar u$. Put $f = u^2/s^2 + s^2/u^2$ (that is $v^2 + v^{-2}$ with $v = u/s$) and let $W$ be the \overline{\mathbb{Q}}-span of $1, u, \bar u, f, f/(s + u)$. Then the five numbers are free over $\overline{\mathbb{Q}}$, and $W$ contains none of $u^2$, $\bar u^2$ and $1/(u - b)$ for non-zero $b \in \overline{\mathbb{Q}}$.
--
--   So $W$ is one of the conjugation-stable configuration spaces $W(1, f)$ that Theorem B does not see. Its polar divisor $2[0] + 2[\infty] + [-s]$ has degree $5$, while the progression spaces invisible to Theorem B have degree $6$, so it contains no $4$-term geometric progression.
--
--   **Proof.** Write $F = u^2/s^2 + s^2/u^2$ and $G = F/(s + u)$; then $s^2u^2F = u^4 + s^4$, $(s + u)G = F$ and $\bar u = s^2/u$. Multiplying a linear relation among $1, u, \bar u, F, G$, or a membership of $u^2$, $\bar u^2$ or $1/(u - b)$, by $s^2u^2(s + u)$ (and by $u - b$) gives a polynomial identity in $u$ of degree at most $6$ over $\overline{\mathbb{Q}}$, which holds identically because $u$ is transcendental. The six coefficient equations force the relation to be trivial; for $u^2$, $\bar u^2$ and $1/(u + s)$ one fixed combination of them leaves a non-zero power of $s$ equal to $0$; for $b \neq -s$, evaluating the identity at $X = b$ leaves $s^2b^2(s + b) = 0$.
--
--   **Novelty.** Not found in the sources read; it is short.
-- source:
--   Not found in the sources read. R11 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 11 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem real_pencil_quartic_space_excludes_squares_and_reciprocals
    (u s : ℂ) (hu : u ∉ Qbar) (hs : s ∈ Qbar) (hsr : conj s = s) (hss : s * s = u * conj u) :
    LinearIndependent (↥Qbar) ![1, u, conj u, (u ^ 2 / (s * s) + s * s / u ^ 2), (u ^ 2 / (s * s) + s * s / u ^ 2) / (s + 1 * u)] ∧
      u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, (u ^ 2 / (s * s) + s * s / u ^ 2), (u ^ 2 / (s * s) + s * s / u ^ 2) / (s + 1 * u)} : Set ℂ) ∧
      conj u ^ 2 ∉ Submodule.span Qbar ({1, u, conj u, (u ^ 2 / (s * s) + s * s / u ^ 2), (u ^ 2 / (s * s) + s * s / u ^ 2) / (s + 1 * u)} : Set ℂ) ∧
      ∀ b ∈ Qbar, b ≠ 0 → (u - b)⁻¹ ∉ Submodule.span Qbar ({1, u, conj u, (u ^ 2 / (s * s) + s * s / u ^ 2), (u ^ 2 / (s * s) + s * s / u ^ 2) / (s + 1 * u)} : Set ℂ) := by
  sorry

end DiazModulus
