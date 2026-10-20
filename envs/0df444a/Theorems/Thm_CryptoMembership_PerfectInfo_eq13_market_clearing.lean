-- Prove2me | Theorems.Thm_CryptoMembership_PerfectInfo_eq13_market_clearing
-- name    : CryptoMembership.PerfectInfo.eq13_market_clearing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:57.335011+00:00
-- url     : https://prove2.me/theorems/add35313-f19b-485d-ad95-b46ed6cc07c7
-- title:
--   Eq. (13), A.2 pp. 32–33 (PDF 33–34) — market clearing ⇔ log P = √(τ_ε/τ_e)(A − A*) − ξ − log(1 − ρ_s)
-- statement:
--   Under the standing assumptions, for every cutoff $A^*$ and every price $P>0$, the mass of households with $A_i\ge A^*$ equals the mass of miners who mine at price $P$ if and only if
--   $$\log P=\sqrt{\frac{\tau_\varepsilon}{\tau_e}}\,(A-A^*)-\xi-\log(1-\rho_s).\tag{13}$$
--
--   Equation (13) is the log-linear price of Proposition 2, part 2.
-- source:
--   Sockin & Xiong, A Model of Cryptocurrencies, preliminary draft (March 2018), A.2, pp. 32–33 (PDF 33–34), eqs. (12)–(13)

import Mathlib
import Definitions.Def_CryptoMembership_PerfectInfo_Model

namespace CryptoMembership.PerfectInfo

theorem eq13_market_clearing (P : Params) (hP : P.Standing) (A xi a price : ℝ)
    (hprice : 0 < price) :
    buyerMass P A (Set.Ici a) = minerMass P xi price ↔
      Real.log price = Real.sqrt (P.tauEps / P.tauE) * (A - a) - xi - Real.log (1 - P.rho) := by sorry

end CryptoMembership.PerfectInfo
