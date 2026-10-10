-- Prove2me | Theorems.Thm_ConservationLaws_momentum_conservation_of_third_law
-- name    : ConservationLaws.momentum_conservation_of_third_law
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:25:50.616339+00:00
-- url     : https://prove2.me/theorems/b7eb62c2-f5f5-44e2-b480-c9b5cd9e1966
-- title:
--   Conservation of momentum from Newton's third law
-- statement:
--   Let $N$ particles in $\mathbb{R}^d$ have masses $m_i > 0$, velocities $v_i(t)$ and accelerations $a_i(t) = \dot v_i(t)$. Suppose the only forces are internal forces $F_{ij}(t)$ (force on $i$ due to $j$) obeying Newton's third law $F_{ij}(t) = -F_{ji}(t)$, and Newton's second law $m_i a_i(t) = \sum_j F_{ij}(t)$ holds. Then the total momentum $P(t) = \sum_i m_i v_i(t)$ is constant: $P(t) = P(s)$ for all $t, s$.
-- source:
--   Wikipedia, "Momentum" (uploaded PDF), https://en.wikipedia.org/wiki/Momentum, section "Conservation" (total change in momentum of interacting particles is zero)

import Mathlib

namespace ConservationLaws

theorem momentum_conservation_of_third_law
    {d N : ℕ} (m : Fin N → ℝ) (hm : ∀ i, 0 < m i)
    (v a : Fin N → ℝ → EuclideanSpace ℝ (Fin d))
    (F : Fin N → Fin N → ℝ → EuclideanSpace ℝ (Fin d))
    (hthird : ∀ i j t, F i j t = -F j i t)
    (hv : ∀ i t, HasDerivAt (v i) (a i t) t)
    (hnewton : ∀ i t, m i • a i t = ∑ j, F i j t) :
    ∀ t s, ∑ i, m i • v i t = ∑ i, m i • v i s := by sorry

end ConservationLaws
