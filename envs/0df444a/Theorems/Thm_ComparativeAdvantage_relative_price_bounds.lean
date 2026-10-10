-- Prove2me | Theorems.Thm_ComparativeAdvantage_relative_price_bounds
-- name    : ComparativeAdvantage.relative_price_bounds
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:26.651973+00:00
-- url     : https://prove2.me/theorems/f49d237a-46fc-4d96-afe7-1a2718ede919
-- title:
--   With finite relative demand, the world relative price lies between the autarky prices
-- statement:
--   Let Home have a comparative advantage in cloth, $a_{LC}/a_{LW}<a'_{LC}/a'_{LW}$, and let $P_C,P_W>0$. Let $(Q_C,Q_W)$ be a competitive output of Home and $(Q'_C,Q'_W)$ a competitive output of Foreign at these prices, and suppose the world supplies of both goods are strictly positive,
--   $$Q_C+Q'_C>0,\qquad Q_W+Q'_W>0,$$
--   as market clearing requires when world relative demand is finite and positive. Then
--   $$\frac{a_{LC}}{a_{LW}}\le\frac{P_C}{P_W}\le\frac{a'_{LC}}{a'_{LW}}.$$
--
--   The equilibrium relative price is therefore always bounded by the two autarky relative prices.
--
--   **Formalization Note** Relative demand is not modelled as a function; "finite relative demand" is encoded by the requirement that world output of both goods be positive.
-- source:
--   Wikipedia, "Comparative advantage" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Comparative_advantage, section "Ricardian model"

import Mathlib
import Definitions.Def_ComparativeAdvantage_Model

namespace ComparativeAdvantage

theorem relative_price_bounds (h f : Country) (hCA : HasComparativeAdvantageInCloth h f)
    (PC PW : ℝ) (hPC : 0 < PC) (hPW : 0 < PW) (qH qF : ℝ × ℝ)
    (hqH : IsCompetitiveOutput h PC PW qH) (hqF : IsCompetitiveOutput f PC PW qF)
    (hcloth : 0 < qH.1 + qF.1) (hwine : 0 < qH.2 + qF.2) :
    h.aLC / h.aLW ≤ PC / PW ∧ PC / PW ≤ f.aLC / f.aLW := by sorry

end ComparativeAdvantage
