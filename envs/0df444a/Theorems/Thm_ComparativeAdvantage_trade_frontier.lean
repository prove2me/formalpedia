-- Prove2me | Theorems.Thm_ComparativeAdvantage_trade_frontier
-- name    : ComparativeAdvantage.trade_frontier
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:31.043013+00:00
-- url     : https://prove2.me/theorems/ec5efa52-3619-45f0-829d-ddff168585ae
-- title:
--   The free-trade consumption possibility frontier lies above the autarky frontier
-- statement:
--   Let a country specialize in cloth and trade at world prices $P_C,P_W>0$ with $a_{LC}/a_{LW}\le P_C/P_W$, so that its consumption satisfies $a_{LC}Q_C+a_{LC}(P_W/P_C)Q_W\le L$. Then
--
--   1. a bundle $(Q_C,Q_W)$ is in its consumption possibility set if and only if $Q_C,Q_W\ge0$ and $$Q_C\le\frac{L}{a_{LC}}-\frac{P_W}{P_C}Q_W;$$
--   2. for every $Q_W\ge0$, $$\frac{L}{a_{LC}}-\frac{a_{LW}}{a_{LC}}Q_W\le\frac{L}{a_{LC}}-\frac{P_W}{P_C}Q_W.$$
--
--   The consumption possibility frontier with trade lies on or above the autarky production possibility frontier.
-- source:
--   Wikipedia, "Comparative advantage" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Comparative_advantage, section "Ricardian model"

import Mathlib
import Definitions.Def_ComparativeAdvantage_Model

namespace ComparativeAdvantage

theorem trade_frontier (c : Country) (PC PW : ℝ) (hPC : 0 < PC) (hPW : 0 < PW)
    (hp : c.aLC / c.aLW ≤ PC / PW) :
    (∀ q : ℝ × ℝ, q ∈ tradeSetCloth c PC PW ↔
      0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 ≤ c.L / c.aLC - (PW / PC) * q.2) ∧
    ∀ QW : ℝ, 0 ≤ QW →
      c.L / c.aLC - (c.aLW / c.aLC) * QW ≤ c.L / c.aLC - (PW / PC) * QW := by sorry

end ComparativeAdvantage
