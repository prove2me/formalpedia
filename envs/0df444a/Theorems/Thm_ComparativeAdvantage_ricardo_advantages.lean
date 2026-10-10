-- Prove2me | Theorems.Thm_ComparativeAdvantage_ricardo_advantages
-- name    : ComparativeAdvantage.ricardo_advantages
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:34:12.394033+00:00
-- url     : https://prove2.me/theorems/9cf014d4-a749-4d8f-a944-f2eaaefeec88
-- title:
--   Ricardo's example: Portugal's absolute advantage, England's comparative advantage in cloth
-- statement:
--   In Ricardo's example England needs $100$ hours of work for one unit of cloth and $120$ for one unit of wine, while Portugal needs $90$ and $80$. Then
--
--   1. Portugal has an absolute advantage in both goods: $90<100$ and $80<120$;
--   2. England has a comparative advantage in cloth: $$\frac{100}{120}<\frac{90}{80};$$
--   3. Portugal does not have a comparative advantage in cloth relative to England.
-- source:
--   Wikipedia, "Comparative advantage" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Comparative_advantage, section "Ricardo's example"

import Mathlib
import Definitions.Def_ComparativeAdvantage_Model

namespace ComparativeAdvantage

theorem ricardo_advantages :
    portugal.aLC < england.aLC ∧ portugal.aLW < england.aLW ∧
    HasComparativeAdvantageInCloth england portugal ∧
    ¬ HasComparativeAdvantageInCloth portugal england := by sorry

end ComparativeAdvantage
