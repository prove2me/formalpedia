-- Prove2me | Theorems.Thm_AlbouyKaloshin_example_masses_one_to_five
-- name    : AlbouyKaloshin.example_masses_one_to_five
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T22:21:43.556012+00:00
-- url     : https://prove2.me/theorems/ba8ccf0b-2817-4c49-8d7e-aaab1be0b73a
-- title:
--   Example: masses $1,2,3,4,5$ give finitely many normalized central configurations
-- statement:
--   For the masses $m_1=1$, $m_2=2$, $m_3=3$, $m_4=4$, $m_5=5$, the planar five-body problem has finitely many normalized central configurations: system (4) with $n=5$ and these masses has finitely many complex solutions.
--
--   This is the first explicit $5$-tuple of positive masses shown to have finitely many planar central configurations.
-- source:
--   A. Albouy and V. Kaloshin, Finiteness of central configurations of five bodies in the plane, Annals of Mathematics 176 (2012), no. 1, 535–588, https://doi.org/10.4007/annals.2012.176.1.10, p. 583, Example

import Mathlib
import Definitions.Def_AlbouyKaloshin_CentralConfigurations

namespace AlbouyKaloshin

theorem example_masses_one_to_five :
    (NormalizedCC 5 (fun k => ((k : ℕ) + 1 : ℂ))).Finite := by sorry

end AlbouyKaloshin
