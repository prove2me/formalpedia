-- Prove2me | Theorems.Thm_ChenWhitt93_Reflection_eq_2_4_fixed_point
-- name    : ChenWhitt93.Reflection.eq_2_4_fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:17:41.067988+00:00
-- url     : https://prove2.me/theorems/ea2b0d9d-a0ef-4884-bb95-6bc93e9bedfb
-- title:
--   Eq. (2.4) — (2.3) is equivalent to the fixed-point equation $y = (Qy - x)^{\uparrow} \vee 0$
-- statement:
--   Let $Q$ be an $n\times n$ real matrix satisfying the standing assumptions of Section 2 ($Q \ge 0$, every column sum at most $1$, $Q^k \to 0$), let $T \in \mathbb R$, and let $x, y \in D([0,T],\mathbb R^n)$ and $z$ satisfy (2.1) and (2.2), that is, $z = x + (I-Q)y \ge 0$ on $[0,T]$ and every $y_j$ is nondecreasing with $y_j(0) = 0$. As noted by Harrison and Reiman, the complementarity condition (2.3) holds if and only if $y$ is a fixed point of $\pi_x$ on $[0,T]$:
--   $$
--   y(t) = \pi_x(y)(t) = \Big(\sup_{0 \le s \le t}\big(Qy(s) - x(s)\big)\Big) \vee 0 \qquad (0 \le t \le T),
--   $$
--   coordinatewise. The paper adds that the Harrison–Reiman argument remains valid for $x \in D$.
--
--   The fixed-point form is what the proofs of Propositions 2.2 and 2.3 work with.
--
--   **Formalization Note** The standing assumptions on $Q$ are kept as a hypothesis, as on the page, although the equivalence is a one-dimensional Skorokhod-problem statement in each coordinate and does not use them. (2.3) is encoded as in the definition file: the Lebesgue–Stieltjes measure $dy_j$ of $\{t\in[0,T]: z_j(t) > 0\}$ is zero.
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), p. 337, Section 2, Eq. (2.4)

import Mathlib
import Definitions.Def_ChenWhitt93_Reflection_Basic
import Definitions.Def_ChenWhitt93_Reflection_ReflectionMap

open Filter Topology Matrix

namespace ChenWhitt93.Reflection

/-- Section 2, Eq. (2.4), p. 337 (as noted by Harrison and Reiman): under the standing
assumptions on `Q`, for `x, y ∈ D` satisfying (2.1)–(2.2), condition (2.3) holds if and only if `y = πₓ(y) = (Qy − x)↑ ∨ 0` on `[0,T]`. -/
theorem eq_2_4_fixed_point {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : IsTransientSubstochasticT Q) (T : ℝ)
    (x y z : ℝ → Fin n → ℝ) (hx : IsCadlagOn T x) (hy : IsCadlagOn T y)
    (h21 : Cond21 Q T x y z) (h22 : Cond22 T y) :
    Cond23 T y z ↔ ∀ t ∈ Set.Icc (0 : ℝ) T, y t = piMap Q x y t := by sorry

end ChenWhitt93.Reflection
