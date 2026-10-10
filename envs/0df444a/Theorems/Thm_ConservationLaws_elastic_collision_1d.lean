-- Prove2me | Theorems.Thm_ConservationLaws_elastic_collision_1d
-- name    : ConservationLaws.elastic_collision_1d
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:27:05.015065+00:00
-- url     : https://prove2.me/theorems/c931c920-cf39-4911-b104-7667607ebf23
-- title:
--   Head-on elastic collision: final velocities
-- statement:
--   Two bodies of masses $m_A, m_B > 0$ collide head-on in one dimension, with velocities $u_A, u_B$ before and $v_A, v_B$ after. If both momentum and kinetic energy are conserved,
--   $$m_A u_A + m_B u_B = m_A v_A + m_B v_B,\qquad \tfrac12 m_A u_A^2 + \tfrac12 m_B u_B^2 = \tfrac12 m_A v_A^2 + \tfrac12 m_B v_B^2,$$
--   then either the velocities are unchanged ($v_A = u_A$, $v_B = u_B$), or
--   $$v_A = \frac{m_A - m_B}{m_A + m_B}u_A + \frac{2m_B}{m_A + m_B}u_B,\qquad v_B = \frac{2m_A}{m_A + m_B}u_A + \frac{m_B - m_A}{m_A + m_B}u_B.$$
-- source:
--   Wikipedia, "Momentum" (uploaded PDF), https://en.wikipedia.org/wiki/Momentum, section "Application to collisions — Elastic collisions" (head-on elastic collision, general final velocities)

import Mathlib

namespace ConservationLaws

theorem elastic_collision_1d
    (mA mB uA uB vA vB : ℝ) (hmA : 0 < mA) (hmB : 0 < mB)
    (hp : mA * uA + mB * uB = mA * vA + mB * vB)
    (hE : (1 / 2 : ℝ) * mA * uA ^ 2 + (1 / 2 : ℝ) * mB * uB ^ 2 =
      (1 / 2 : ℝ) * mA * vA ^ 2 + (1 / 2 : ℝ) * mB * vB ^ 2) :
    (vA = uA ∧ vB = uB) ∨
    (vA = ((mA - mB) * uA + 2 * mB * uB) / (mA + mB) ∧
     vB = (2 * mA * uA + (mB - mA) * uB) / (mA + mB)) := by sorry

end ConservationLaws
