-- Prove2me | Theorems.Thm_ConservationLaws_perfectly_inelastic_collision_1d
-- name    : ConservationLaws.perfectly_inelastic_collision_1d
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:27:23.395279+00:00
-- url     : https://prove2.me/theorems/a333ca2a-4641-4a94-8f51-582983022cbb
-- title:
--   Perfectly inelastic collision: common velocity and kinetic energy lost
-- statement:
--   Two bodies of masses $m_A, m_B > 0$ with velocities $u_A, u_B$ collide perfectly inelastically in one dimension and move afterwards with a common velocity $w$. If momentum is conserved, $m_A u_A + m_B u_B = (m_A + m_B) w$, then
--   $$w = \frac{m_A u_A + m_B u_B}{m_A + m_B},$$
--   and the kinetic energy lost is
--   $$\Big(\tfrac12 m_A u_A^2 + \tfrac12 m_B u_B^2\Big) - \tfrac12 (m_A + m_B) w^2 = \tfrac12\,\frac{m_A m_B}{m_A + m_B}\,(u_A - u_B)^2 \;\ge 0.$$
-- source:
--   Wikipedia, "Momentum" (uploaded PDF), https://en.wikipedia.org/wiki/Momentum, section "Application to collisions — Inelastic collisions" (perfectly inelastic collision, conservation of momentum, kinetic energy converted to other forms)

import Mathlib

namespace ConservationLaws

theorem perfectly_inelastic_collision_1d
    (mA mB uA uB w : ℝ) (hmA : 0 < mA) (hmB : 0 < mB)
    (hp : mA * uA + mB * uB = (mA + mB) * w) :
    w = (mA * uA + mB * uB) / (mA + mB) ∧
    ((1 / 2 : ℝ) * mA * uA ^ 2 + (1 / 2 : ℝ) * mB * uB ^ 2) - (1 / 2 : ℝ) * (mA + mB) * w ^ 2 =
      (1 / 2 : ℝ) * (mA * mB / (mA + mB)) * (uA - uB) ^ 2 := by sorry

end ConservationLaws
