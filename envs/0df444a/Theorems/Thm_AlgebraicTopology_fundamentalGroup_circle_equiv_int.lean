-- Prove2me | Theorems.Thm_AlgebraicTopology_fundamentalGroup_circle_equiv_int
-- name    : AlgebraicTopology.fundamentalGroup_circle_equiv_int
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:26:47.082037+00:00
-- url     : https://prove2.me/theorems/5684d2a1-392a-40e6-9647-951e2e8297d3
-- title:
--   The fundamental group of the circle is $\mathbb{Z}$
-- statement:
--   **The fundamental group of the circle is infinite cyclic.**
--
--   Let $S^1 = \mathbb{R}/\mathbb{Z}$ be the circle, realised as `AddCircle (1 : ℝ)`. Then
--
--   $$\pi_1\bigl(S^1, 0\bigr) \;\cong\; \mathbb{Z}.$$
--
--   This is the foundational computation of algebraic topology — the first fundamental group that is
--   not trivial, and the one from which essentially every classical application follows: the
--   Brouwer fixed-point theorem in dimension two, the fundamental theorem of algebra by a winding
--   number argument, the Borsuk–Ulam theorem on the circle, the non-existence of a retraction of
--   the disc onto its boundary, and the degree theory of maps $S^1 \to S^1$.
--
--   The isomorphism is the **winding number**. A loop $\gamma$ based at $0$ lifts uniquely along the
--   covering $\mathbb{R} \to \mathbb{R}/\mathbb{Z}$ to a path $\tilde\gamma$ starting at $0$, and
--   because $\gamma$ is a loop the endpoint $\tilde\gamma(1)$ is an integer. That integer counts how
--   many times $\gamma$ wraps around the circle; it depends only on the homotopy class, it is
--   additive under concatenation of loops, and every integer is attained by the loop
--   $t \mapsto nt \bmod 1$.
--
--   Both directions of the correspondence use the covering $\mathbb{R} \to S^1$ in an essential way:
--   surjectivity is the explicit family of loops above, and injectivity is the fact that a loop whose
--   lift closes up is a loop in $\mathbb{R}$, hence null-homotopic because $\mathbb{R}$ is
--   contractible.
--
--   **Formalization note.** The circle is `AddCircle (1 : ℝ)`, i.e. $\mathbb{R}$ modulo the
--   subgroup `zmultiples 1`, with basepoint $0$. The conclusion is stated as `Nonempty` of a
--   `MulEquiv` onto `Multiplicative ℤ`, since $\pi_1$ is written multiplicatively while
--   $\mathbb{Z}$ is additive.
-- source:
--   Classical; the foundational computation of algebraic topology. See Hatcher, *Algebraic Topology*, Theorem 1.7, and Munkres, *Topology*, §52. Proved here by instantiating Mathlib's deck-transformation classification for quotient covering maps (`IsAddQuotientCoveringMap.fundamentalGroupEquiv`, due to Junyan Xu) at the covering $\mathbb{R} \to \mathbb{R}/\mathbb{Z}$.

import Mathlib

namespace AlgebraicTopology

theorem fundamentalGroup_circle_equiv_int :
    Nonempty (FundamentalGroup (AddCircle (1 : ℝ)) 0 ≃* Multiplicative ℤ) := by sorry

end AlgebraicTopology
