-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_cro_coeff_lin
-- name    : Formalism.L2.Pj.Crude.cro_coeff_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:55.941799+00:00
-- url     : https://prove2.me/theorems/4f18278b-cf75-49f0-a55e-b5ee7daf803f
-- title:
--   Crude: cro coeff lin
-- statement:
--   The Crude construction uses the cro coeff lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L138-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L138-L227

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

theorem Formalism.L2.Pj.Crude.cro_coeff_lin (G : FGLaw k d) (i j : Fin d) :
    coeff (Finsupp.single ((1 : Fin 2), i) 1) (G.F j) = if i = j then 1 else 0 := by sorry
