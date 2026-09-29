-- Prove2me | Theorems.Thm_Diaz_second_difference_mem
-- name    : Diaz.second_difference_mem
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:17:33.78782+00:00
-- url     : https://prove2.me/theorems/31424ad8-e928-45ae-9f8c-d2550c75b3a7
-- title:
--   Three values of a quadratic pin down its leading coefficient
-- statement:
--   Let $K \subseteq \mathbb{C}$ be a subfield, let $\rho, c, d \in \mathbb{C}$, and put $q_n = \rho + cn + dn^2$. If $q_{n_1}, q_{n_2}, q_{n_3} \in K$ for three pairwise distinct integers $n_1, n_2, n_3$, then $d \in K$.
--
--   **Where this sits.** This is the arithmetic core of the proof of Theorem 3.3 (*Fibres*), the two-point algebraic-fibre bound, of the note cited below, isolated from the transcendence input. That proof amounts to the identity
--
--   $$\frac{1}{n_3-n_2}\left(\frac{q_{n_3}-q_{n_1}}{n_3-n_1} - \frac{q_{n_2}-q_{n_1}}{n_2-n_1}\right) = 4\pi^2,$$
--
--   with $q_n = |u|^2 + 4\pi n y + 4\pi^2 n^2$ the squared moduli along an exponential fibre. The statement above is that identity with $4\pi^2$ replaced by an arbitrary leading coefficient $d$ and $\bar{\mathbb{Q}}$ by an arbitrary subfield: the divided second difference of a quadratic is its leading coefficient, and a subfield is closed under the operations used to form it.
--
--   **Proof.** Both inner quotients equal $c + d(n_i + n_j)$; their difference is $d(n_3-n_2)$. The Lean checks the resulting closed formula for $d$ by `field_simp; ring` and then reads off membership from the subfield axioms, using that the integer casts are non-zero because the indices are distinct.
--
--   Elementary and certainly classical; recorded because the fibre bound is proved with it.
--
--   **Source.** Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), proof of Theorem 3.3. The mathematics is his; this node only records one step of it in Lean, and claims no novelty of its own.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.second_difference_mem {K : Subfield ℂ} {c d ρ : ℂ} {n₁ n₂ n₃ : ℤ}
    (h12 : n₁ ≠ n₂) (h13 : n₁ ≠ n₃) (h23 : n₂ ≠ n₃)
    (h1 : ρ + c * n₁ + d * n₁ ^ 2 ∈ K)
    (h2 : ρ + c * n₂ + d * n₂ ^ 2 ∈ K)
    (h3 : ρ + c * n₃ + d * n₃ ^ 2 ∈ K) : d ∈ K := by sorry
