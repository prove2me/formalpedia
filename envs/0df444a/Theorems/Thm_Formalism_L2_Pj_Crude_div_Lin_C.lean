-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_div_Lin_C
-- name    : Formalism.L2.Pj.Crude.div_Lin_C
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:40:55.797838+00:00
-- url     : https://prove2.me/theorems/a34164fb-de49-4ea4-9709-b6b76ae0fba5
-- title:
--   Crude: div Lin C
-- statement:
--   The Crude construction uses the div Lin C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeDiv.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeDiv.lean#L24-L25

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}

theorem Formalism.L2.Pj.Crude.div_Lin_C (b : Fin n) (v : Fin d → k) (c : k) : Lin b v (C c : PS k n d) = 0 := by sorry
