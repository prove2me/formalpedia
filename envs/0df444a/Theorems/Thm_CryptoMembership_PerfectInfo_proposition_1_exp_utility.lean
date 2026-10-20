-- Prove2me | Theorems.Thm_CryptoMembership_PerfectInfo_proposition_1_exp_utility
-- name    : CryptoMembership.PerfectInfo.proposition_1_exp_utility
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:52.135988+00:00
-- url     : https://prove2.me/theorems/037b8726-7f0e-4428-9371-2ab319dab2eb
-- title:
--   Proposition 1 (perfect-information form, A.2 p. 32) — E[U_i | I_i] = e^{(1−η_c)A_i+η_cA+η_c²/(2τ_ε)} Φ(η_cτ_ε^{−1/2} + (A − A*)τ_ε^{1/2})
-- statement:
--   Under the standing assumptions, let the households that buy the currency be those with endowment exponent at least a cutoff $A^*$. Then a buying household with endowment exponent $A_i$, which observes $A$, has expected utility
--   $$E[U_i\mid\mathcal I_i]=e^{(1-\eta_c)A_i+\eta_cA+\frac12\eta_c^2\tau_\varepsilon^{-1}}\,\Phi\Big(\eta_c\tau_\varepsilon^{-1/2}+\frac{A-A^*}{\tau_\varepsilon^{-1/2}}\Big),$$
--   where the expectation is over the partner's endowment exponent $A_j=A+\varepsilon$, $\varepsilon\sim N(0,\tau_\varepsilon^{-1})$, and the realized utility is $e^{(1-\eta_c)A_i+\eta_cA_j}$ if $A_j\ge A^*$ and $0$ otherwise.
--
--   This closed form is the demand side of every equilibrium condition in the perfect-information setting.
-- source:
--   Sockin & Xiong, A Model of Cryptocurrencies, preliminary draft (March 2018), A.2, p. 32 (PDF 33), display before (11) (perfect-information form of Proposition 1, p. 14)

import Mathlib
import Definitions.Def_CryptoMembership_PerfectInfo_Model

namespace CryptoMembership.PerfectInfo

theorem proposition_1_exp_utility (P : Params) (hP : P.Standing) (A a aStar : ℝ) :
    expUtility P A (Set.Ici aStar) a =
      Real.exp ((1 - P.eta) * a + P.eta * A + P.eta ^ 2 / (2 * P.tauEps)) *
        Phi (P.eta / Real.sqrt P.tauEps + Real.sqrt P.tauEps * (A - aStar)) := by sorry

end CryptoMembership.PerfectInfo
