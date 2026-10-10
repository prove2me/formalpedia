-- Prove2me | Theorems.Thm_ComparativeAdvantage_terms_of_trade_iff
-- name    : ComparativeAdvantage.terms_of_trade_iff
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:33:36.236755+00:00
-- url     : https://prove2.me/theorems/8d3b681e-bb36-470a-b45d-5eef3335f7bc
-- title:
--   Terms of trade: specialization pays exactly when the world price beats the opportunity cost
-- statement:
--   Let a country have unit labour requirements $a_{LC},a_{LW}>0$ and labour force $L>0$, and let world prices be $P_C,P_W>0$.
--
--   1. Its autarky set is contained in its consumption set when it specializes in cloth if and only if $$\frac{a_{LC}}{a_{LW}}\le\frac{P_C}{P_W}.$$
--   2. Its autarky set is contained in its consumption set when it specializes in wine if and only if $$\frac{P_C}{P_W}\le\frac{a_{LC}}{a_{LW}}.$$
--
--   Hence terms of trade that benefit both a cloth exporter and a wine exporter lie between the two countries' opportunity costs.
-- source:
--   Wikipedia, "Comparative advantage" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Comparative_advantage, section "Terms of trade"

import Mathlib
import Definitions.Def_ComparativeAdvantage_Model

namespace ComparativeAdvantage

theorem terms_of_trade_iff (c : Country) (PC PW : ℝ) (hPC : 0 < PC) (hPW : 0 < PW) :
    (autarkySet c ⊆ tradeSetCloth c PC PW ↔ c.aLC / c.aLW ≤ PC / PW) ∧
    (autarkySet c ⊆ tradeSetWine c PC PW ↔ PC / PW ≤ c.aLC / c.aLW) := by sorry

end ComparativeAdvantage
