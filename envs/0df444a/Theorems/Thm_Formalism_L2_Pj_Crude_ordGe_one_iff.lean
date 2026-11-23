-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_ordGe_one_iff
-- name    : Formalism.L2.Pj.Crude.ordGe_one_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:40:15.450368+00:00
-- url     : https://prove2.me/theorems/a5ea8a53-cace-496f-90ba-de8df0c7a311
-- title:
--   Crude: ord Ge one iff
-- statement:
--   The Crude construction uses the ord Ge one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L13-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L13-L29

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}

theorem Formalism.L2.Pj.Crude.ordGe_one_iff (f : PS k n d) : OrdGe 1 f ↔ constantCoeff f = 0 := by sorry
