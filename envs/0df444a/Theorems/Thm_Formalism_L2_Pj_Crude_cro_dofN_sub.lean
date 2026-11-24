-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_cro_dofN_sub
-- name    : Formalism.L2.Pj.Crude.cro_dofN_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:35.794182+00:00
-- url     : https://prove2.me/theorems/4aea9e82-839f-4f86-b891-1afd31e939fa
-- title:
--   Crude: cro dof N sub
-- statement:
--   The Crude construction uses the cro dof N sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L317-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L317-L320

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

theorem Formalism.L2.Pj.Crude.cro_dofN_sub (F : Fin d → PS k 2 d) (b : Fin n) (v : Fin d → k) (X Y : PS k n d) :
    DofN F b v (X - Y) = DofN F b v X - DofN F b v Y := by sorry
