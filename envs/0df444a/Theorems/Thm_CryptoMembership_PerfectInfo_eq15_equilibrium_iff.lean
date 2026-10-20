-- Prove2me | Theorems.Thm_CryptoMembership_PerfectInfo_eq15_equilibrium_iff
-- name    : CryptoMembership.PerfectInfo.eq15_equilibrium_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:49.3605+00:00
-- url     : https://prove2.me/theorems/74d5709d-1285-458d-b0cb-871449e4bfc4
-- title:
--   Eq. (15), A.2 p. 33 (PDF 34) — ([A*,∞), P) is an equilibrium ⇔ P > 0, s = A* − A solves (15), and P is given by (13)
-- statement:
--   Under the standing assumptions, the cutoff purchase set $[A^*,\infty)$ together with a price $P$ is an equilibrium if and only if $P>0$, the price satisfies (13), and $s=A^*-A$ solves
--   $$e^{(1-\eta_c+\sqrt{\tau_\varepsilon/\tau_e})s}\,\Phi\Big(\eta_c\tau_\varepsilon^{-1/2}-\frac{s}{\tau_\varepsilon^{-1/2}}\Big)=e^{-A-\xi-\frac12\eta_c^2\tau_\varepsilon^{-1}-\log(1-\rho_s)}.\tag{15}$$
--
--   Together with the optimality of cutoff strategies, this reduces the equilibria to the roots of a single scalar equation whose left-hand side does not depend on $(A,\xi)$.
-- source:
--   Sockin & Xiong, A Model of Cryptocurrencies, preliminary draft (March 2018), A.2, pp. 32–33 (PDF 33–34), eqs. (11), (13), (14), (15); equation (6) of Proposition 2, p. 15 (PDF 16)

import Mathlib
import Definitions.Def_CryptoMembership_PerfectInfo_Model

namespace CryptoMembership.PerfectInfo

theorem eq15_equilibrium_iff (P : Params) (hP : P.Standing) (A xi a price : ℝ) :
    IsEquilibrium P A xi (Set.Ici a) price ↔
      0 < price ∧ lhs15 P (a - A) = rhs15 P A xi ∧
        Real.log price = Real.sqrt (P.tauEps / P.tauE) * (A - a) - xi - Real.log (1 - P.rho) := by sorry

end CryptoMembership.PerfectInfo
