-- Prove2me | Theorems.Thm_ComparativeAdvantage_autarky_frontier
-- name    : ComparativeAdvantage.autarky_frontier
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:47.595105+00:00
-- url     : https://prove2.me/theorems/eb1def20-4daf-495a-849e-4616c34e6afe
-- title:
--   The autarky production possibility frontier
-- statement:
--   In autarky a country faces the production constraint $a_{LC}Q_C+a_{LW}Q_W\le L$ with $Q_C,Q_W\ge0$. Then
--
--   1. every feasible bundle satisfies $$Q_C\le\frac{L}{a_{LC}}-\frac{a_{LW}}{a_{LC}}Q_W;$$
--   2. for every $Q_W$ with $0\le Q_W\le L/a_{LW}$, the bundle $\bigl(L/a_{LC}-(a_{LW}/a_{LC})Q_W,\;Q_W\bigr)$ is feasible.
--
--   So cloth consumption at the production possibility frontier is $Q_C=L/a_{LC}-(a_{LW}/a_{LC})Q_W$.
-- source:
--   Wikipedia, "Comparative advantage" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Comparative_advantage, section "Ricardian model"

import Mathlib
import Definitions.Def_ComparativeAdvantage_Model

namespace ComparativeAdvantage

theorem autarky_frontier (c : Country) :
    (∀ q ∈ autarkySet c, q.1 ≤ c.L / c.aLC - (c.aLW / c.aLC) * q.2) ∧
    ∀ QW : ℝ, 0 ≤ QW → QW ≤ c.L / c.aLW →
      (c.L / c.aLC - (c.aLW / c.aLC) * QW, QW) ∈ autarkySet c := by sorry

end ComparativeAdvantage
