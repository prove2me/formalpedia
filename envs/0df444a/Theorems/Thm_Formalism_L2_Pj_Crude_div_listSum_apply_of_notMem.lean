-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_div_listSum_apply_of_notMem
-- name    : Formalism.L2.Pj.Crude.div_listSum_apply_of_notMem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:13.469031+00:00
-- url     : https://prove2.me/theorems/eba49511-d3f5-4c65-874b-bd72b838893e
-- title:
--   Crude: div list Sum apply of not Mem
-- statement:
--   The Crude construction uses the div list Sum apply of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeDiv.lean#L148-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeDiv.lean#L148-L154

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

theorem Formalism.L2.Pj.Crude.div_listSum_apply_of_notMem {ι : Type} (a : ι →₀ ℕ) (L : List ι) (l : ι) (hl : l ∉ L) :
    (L.map fun l' => Finsupp.single l' (a l')).sum l = 0 := by sorry
