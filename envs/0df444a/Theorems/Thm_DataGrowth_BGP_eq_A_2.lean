-- Prove2me | Theorems.Thm_DataGrowth_BGP_eq_A_2
-- name    : DataGrowth.BGP.eq_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:00.114991+00:00
-- url     : https://prove2.me/theorems/7ac43ea4-8c1c-45f8-9c15-5012e02d50c5
-- title:
--   (A.2), PDF p. 24 — on a decentralized BGP, $V=\pi/(r^*-n)$ and $\dot V/V=n$
-- statement:
--   Assume the standing parameter ranges and let $(c,\phi,N,l_R,l_E,V,w,p_\phi,r,\pi)$ be a balanced growth path of the decentralized economy, with constant interest rate $r^*$ and growth rate $g_V$ of the patent value. Then for every $t>0$
--   $$
--   V(t)=\frac{\pi(t)}{r^*-n},\qquad\text{and}\qquad g_V=n .
--   $$
--
--   The present value (9) of a profit stream growing at the population rate $n$ is a constant multiple of current profit; this is the step (A.2) of the proof of Proposition 1.
--
--   **Formalization Note** $r^*>n$ is not assumed: it follows from the integrability of the present-value integrand, which is part of the equilibrium condition (9).
-- source:
--   Cong, Xie, Zhang, Knowledge Accumulation, Privacy, and Growth in a Data Economy, arXiv:2109.10028v1, p. 24 (Online Appendix p. 1), (A.2)

import Mathlib
import Definitions.Def_DataGrowth_BGP_DecEconomy

namespace DataGrowth.BGP

/-- Cong, Xie, Zhang, *Knowledge Accumulation, Privacy, and Growth in a Data Economy*, arXiv:2109.10028v1, PDF p. 24 (Online Appendix p. 1), (A.2): on a balanced growth path of the
decentralized economy, r(t) = r*, the patent value (9) reduces to V(t) = π(t)/(r* − n), and the
growth rate of V is V̇/V = π̇/π = n.

Formalization Note: r* > n is not assumed; it follows from the integrability of the present-value
integrand, which is part of the equilibrium condition (9) in `IsDecEq`. The BGP reading (each
variable at its own constant growth rate, r constant, g_c = g_y) and the level-form equilibrium
encoding are those of `IsDecBGP`. -/
theorem eq_A_2 (P : Params) (hP : P.Standing) (E : DecPath) (R : DecRates)
    (hE : IsDecBGP P E R) :
    (∀ t : ℝ, 0 < t → E.V t = E.pi t / (R.rstar - P.n)) ∧ R.gV = P.n := by sorry

end DataGrowth.BGP
