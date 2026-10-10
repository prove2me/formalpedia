-- Prove2me | Theorems.Thm_ComparativeAdvantage_comparative_advantage_iff
-- name    : ComparativeAdvantage.comparative_advantage_iff
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:07.871879+00:00
-- url     : https://prove2.me/theorems/7cc1d7bc-02ac-4e53-bd19-bff469bcb0e8
-- title:
--   Two equivalent forms of comparative advantage in cloth
-- statement:
--   Let Home have unit labour requirements $a_{LC},a_{LW}>0$ and Foreign $a'_{LC},a'_{LW}>0$. Home is relatively more productive than Foreign in cloth versus wine if and only if Home has a lower opportunity cost of cloth in terms of wine:
--   $$\frac{a_{LC}}{a'_{LC}}<\frac{a_{LW}}{a'_{LW}}\iff\frac{a_{LC}}{a_{LW}}<\frac{a'_{LC}}{a'_{LW}}.$$
--
--   This lets the comparative-advantage assumption be used in whichever form is convenient.
-- source:
--   Wikipedia, "Comparative advantage" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Comparative_advantage, section "Ricardian model"

import Mathlib
import Definitions.Def_ComparativeAdvantage_Model

namespace ComparativeAdvantage

theorem comparative_advantage_iff (h f : Country) :
    h.aLC / f.aLC < h.aLW / f.aLW ↔ HasComparativeAdvantageInCloth h f := by sorry

end ComparativeAdvantage
