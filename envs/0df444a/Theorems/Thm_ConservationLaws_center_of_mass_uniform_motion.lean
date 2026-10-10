-- Prove2me | Theorems.Thm_ConservationLaws_center_of_mass_uniform_motion
-- name    : ConservationLaws.center_of_mass_uniform_motion
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:26:05.416086+00:00
-- url     : https://prove2.me/theorems/4f69623a-98d8-49e7-98e7-2df3c206e8ec
-- title:
--   The centre of mass of an isolated system moves uniformly with velocity $P/M$
-- statement:
--   Under the hypotheses of the momentum conservation milestone (masses $m_i > 0$, internal forces obeying $F_{ij} = -F_{ji}$, Newton's second law), and with at least one particle, let $M = \sum_i m_i$ be the total mass and $R(t) = M^{-1}\sum_i m_i x_i(t)$ the centre of mass. Then
--   $$R(t) = R(0) + t\,\frac{P(0)}{M}, \qquad P(0) = \sum_i m_i v_i(0),$$
--   i.e. the centre of mass moves in a straight line at constant velocity $v_{\mathrm{cm}} = P/M$ (equivalently $P = M v_{\mathrm{cm}}$).
-- source:
--   Wikipedia, "Momentum" (uploaded PDF), https://en.wikipedia.org/wiki/Momentum, section "Many particles" (centre of mass, $p = m\,v_{cm}$, Euler's first law) and section "Conservation"

import Mathlib

namespace ConservationLaws

theorem center_of_mass_uniform_motion
    {d N : ℕ} (hN : 0 < N) (m : Fin N → ℝ) (hm : ∀ i, 0 < m i)
    (x v a : Fin N → ℝ → EuclideanSpace ℝ (Fin d))
    (F : Fin N → Fin N → ℝ → EuclideanSpace ℝ (Fin d))
    (hthird : ∀ i j t, F i j t = -F j i t)
    (hx : ∀ i t, HasDerivAt (x i) (v i t) t)
    (hv : ∀ i t, HasDerivAt (v i) (a i t) t)
    (hnewton : ∀ i t, m i • a i t = ∑ j, F i j t) :
    ∀ t, (∑ i, m i)⁻¹ • ∑ i, m i • x i t =
      (∑ i, m i)⁻¹ • ∑ i, m i • x i 0 + t • ((∑ i, m i)⁻¹ • ∑ i, m i • v i 0) := by sorry

end ConservationLaws
