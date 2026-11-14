-- Prove2me | Theorems.Thm_APFB01_read_eq_of_descends
-- name    : APFB01.read_eq_of_descends
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:45:38.660185+00:00
-- url     : https://prove2.me/theorems/91b381dc-5ca9-4f83-9140-e40d0ca1e366
-- title:
--   If the truth of a Boolean reading descends, two raw states with equal profiles have equal readings
-- statement:
--   If the truth of a Boolean reading descends, two raw states with equal profiles have equal readings.
-- source:
--   Paper 1 Supplement v9.28:1313-1322,1761-1766,1774-1885,2624-2625,2777-2782,7101

import Definitions.Def_APF_B01_DeclaredInput

set_option autoImplicit false
universe uX uP uF uR uO uA uM

namespace APFB01
end APFB01
open APFB01

theorem APFB01.read_eq_of_descends {X : Type uX} {Process : Type uP}
    (profile : X → Process → Prop) (read : X → Bool)
    (hd : Descends profile (fun x => read x = true))
    (x y : X) (hxy : profile x = profile y) : read x = read y := by sorry
