-- Prove2me | Theorems.Thm_CryptoMembership_PerfectInfo_proposition_1_ex_ante_utility
-- name    : CryptoMembership.PerfectInfo.proposition_1_ex_ante_utility
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:51.0149+00:00
-- url     : https://prove2.me/theorems/57f2add0-a7ad-4095-b327-b987143f8837
-- title:
--   Proposition 1, p. 14 (PDF 15) — ex ante utility U₀ in closed form at an indifference cutoff A*
-- statement:
--   Under the standing assumptions, let the purchase set be $\{A_i\ge A^*\}$ and let the price $P$ be such that the household at the cutoff is indifferent, $E[U_i\mid\mathcal I_i]\big|_{A_i=A^*}=P$ (equation (11)). Then the ex ante utility $U_0=E\big[\max\{E[U_i\mid\mathcal I_i]-P,0\}\big]$, averaged over $A_i\sim N(A,\tau_\varepsilon^{-1})$, equals
--   $$U_0=e^{A+\frac12((1-\eta_c)^2+\eta_c^2)\tau_\varepsilon^{-1}}\,\Phi\Big((1-\eta_c)\tau_\varepsilon^{-1/2}+\frac{A-A^*}{\tau_\varepsilon^{-1/2}}\Big)\Phi\Big(\eta_c\tau_\varepsilon^{-1/2}+\frac{A-A^*}{\tau_\varepsilon^{-1/2}}\Big)-P\,\Phi\Big(\frac{A-A^*}{\tau_\varepsilon^{-1/2}}\Big).$$
--
--   This is the welfare measure whose comparative statics appear in Proposition 2, part 3.
--
--   **Formalization Note** The page's formula replaces $\max\{E[U_i\mid\mathcal I_i]-P,0\}$ by $(E[U_i\mid\mathcal I_i]-P)\mathbf 1\{A_i\ge A^*\}$, which is valid exactly when the cutoff household is indifferent. That condition, which holds in every equilibrium, is stated as a hypothesis; without it the identity is false.
-- source:
--   Sockin & Xiong, A Model of Cryptocurrencies, preliminary draft (March 2018), p. 14 (PDF 15), Proposition 1 (U₀); A.1, p. 32 (PDF 33); A.2, p. 32 (PDF 33), eq. (11)

import Mathlib
import Definitions.Def_CryptoMembership_PerfectInfo_Model

namespace CryptoMembership.PerfectInfo

theorem proposition_1_ex_ante_utility (P : Params) (hP : P.Standing) (A a price : ℝ)
    (hindiff : expUtility P A (Set.Ici a) a = price) :
    exAnteUtility P A (Set.Ici a) price =
      Real.exp (A + ((1 - P.eta) ^ 2 + P.eta ^ 2) / (2 * P.tauEps)) *
          Phi ((1 - P.eta) / Real.sqrt P.tauEps + Real.sqrt P.tauEps * (A - a)) *
          Phi (P.eta / Real.sqrt P.tauEps + Real.sqrt P.tauEps * (A - a)) -
        price * Phi (Real.sqrt P.tauEps * (A - a)) := by sorry

end CryptoMembership.PerfectInfo
