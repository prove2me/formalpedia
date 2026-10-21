-- Prove2me | Theorems.Thm_DataTrackComp_Surplus_theorem_2
-- name    : DataTrackComp.Surplus.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:41.188345+00:00
-- url     : https://prove2.me/theorems/63a1c977-5976-46b6-a8d4-26f282985060
-- title:
--   Theorem 2, p. 18 — for m ∈ (0, m_L), aggregate consumer surplus is higher with data tracking, for myopic and forward-looking consumers
-- statement:
--   Let $\bar u>0$ be the baseline utility and let $m\in(0,m_L)$ be the value of consumer data, where $m_L$ is the upper end of the interior-equilibrium regime (B.32). Then equilibria exist in all three settings: forward-looking, myopic and restricted. For every forward-looking equilibrium, every myopic equilibrium and every restricted equilibrium, the aggregate consumer surplus satisfies
--   $$CS^R<CS^M\qquad\text{and}\qquad CS^R<CS^{FL}.$$
--   That is, data tracking raises aggregate consumer surplus, whether consumers are myopic or forward-looking.
--
--   This is the paper's headline result. Although tracking lets firm B charge tracked consumers their full product-2 valuation, competition for product 1 more than compensates them, as long as the market stays in the interior regime.
--
--   **Formalization Note.** Equilibria are the perfect Bayesian equilibria of the model file, quantified over all continuations. Consumer surplus is the $\mu_0$-expectation of realized utility along the equilibrium path, not the closed forms (C.1) and (C.3). The three existence conjuncts keep the comparison from being vacuous. "$m<m_L$" is the `sSup`-free predicate `InInteriorRegime`.
-- source:
--   Bimpikis, Morgenstern & Saban, Data Tracking under Competition, authors' manuscript with online appendix (Operations Research, doi:10.1287/opre.2023.2489; PDF of 2023-05-04), p. 18 (PDF 18), Theorem 2

import Mathlib
import Definitions.Def_DataTrackComp_Surplus_Game
import Definitions.Def_DataTrackComp_Surplus_ReducedGame

namespace DataTrackComp.Surplus

theorem theorem_2 (ubar m : ℝ) (hu : 0 < ubar) (hm : 0 < m) (hmL : InInteriorRegime m) :
    (∃ E : Assessment, IsEquilibrium .forward ubar m E) ∧
    (∃ E : Assessment, IsEquilibrium .myopic ubar m E) ∧
    (∃ E : Assessment, IsEquilibrium .restricted ubar m E) ∧
    ∀ EF EM ER : Assessment, IsEquilibrium .forward ubar m EF → IsEquilibrium .myopic ubar m EM →
      IsEquilibrium .restricted ubar m ER →
      consumerSurplus .restricted ubar m ER < consumerSurplus .myopic ubar m EM ∧
      consumerSurplus .restricted ubar m ER < consumerSurplus .forward ubar m EF := by sorry

end DataTrackComp.Surplus
