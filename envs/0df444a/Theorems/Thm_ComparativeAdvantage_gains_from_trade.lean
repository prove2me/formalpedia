-- Prove2me | Theorems.Thm_ComparativeAdvantage_gains_from_trade
-- name    : ComparativeAdvantage.gains_from_trade
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:35:49.386737+00:00
-- url     : https://prove2.me/theorems/65dfb7c7-f3e6-42c0-bb75-e04332c1662f
-- title:
--   Gains from trade: specialization by comparative advantage expands both countries' consumption possibilities
-- statement:
--   Let Home and Foreign be two countries of the Ricardian model, Home with labour force $L$ and unit labour requirements $a_{LC},a_{LW}$, Foreign with $L',a'_{LC},a'_{LW}$ (all positive), and suppose Home has a comparative advantage in cloth, $a_{LC}/a_{LW}<a'_{LC}/a'_{LW}$. Let world prices $P_C,P_W>0$ satisfy
--   $$\frac{a_{LC}}{a_{LW}}\le\frac{P_C}{P_W}\le\frac{a'_{LC}}{a'_{LW}}.$$
--   Then
--
--   1. every bundle Home can produce in autarky, $a_{LC}Q_C+a_{LW}Q_W\le L$, can be consumed by Home when it produces only cloth and trades, $a_{LC}Q_C+a_{LC}(P_W/P_C)Q_W\le L$;
--   2. every bundle Foreign can produce in autarky can be consumed by Foreign when it produces only wine and trades, $a'_{LW}(P_C/P_W)Q_C+a'_{LW}Q_W\le L'$;
--   3. if $a_{LC}/a_{LW}<P_C/P_W$, Home's inclusion is strict;
--   4. if $P_C/P_W<a'_{LC}/a'_{LW}$, Foreign's inclusion is strict.
--
--   By trading and specializing in the good of its comparative advantage, each country can expand its consumption possibilities and choose bundles it could not have produced in a closed economy.
--
--   **Formalization Note** The comparative-advantage hypothesis is the standing assumption of the source section; the two price bounds already imply its non-strict form.
-- source:
--   Wikipedia, "Comparative advantage" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Comparative_advantage, section "Ricardian model"

import Mathlib
import Definitions.Def_ComparativeAdvantage_Model

namespace ComparativeAdvantage

theorem gains_from_trade (h f : Country) (hCA : HasComparativeAdvantageInCloth h f)
    (PC PW : ℝ) (hPC : 0 < PC) (hPW : 0 < PW)
    (hlow : h.aLC / h.aLW ≤ PC / PW) (hhigh : PC / PW ≤ f.aLC / f.aLW) :
    autarkySet h ⊆ tradeSetCloth h PC PW ∧ autarkySet f ⊆ tradeSetWine f PC PW ∧
    (h.aLC / h.aLW < PC / PW → autarkySet h ⊂ tradeSetCloth h PC PW) ∧
    (PC / PW < f.aLC / f.aLW → autarkySet f ⊂ tradeSetWine f PC PW) := by sorry

end ComparativeAdvantage
