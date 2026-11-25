-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_Filt_inf_relIndex_of_le
-- name    : Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.inf_relIndex_of_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:45:16.12868+00:00
-- url     : https://prove2.me/theorems/4598d9e1-489b-465f-bf51-94f589debc64
-- title:
--   Filt: inf rel Index of le
-- statement:
--   The Filt construction uses the inf rel Index of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RelativeIndexFlags/RelIndexEqIndexOfMul.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RelativeIndexFlags/RelIndexEqIndexOfMul.lean#L42-L48

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_RelIndexEqIndexOfMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RelativeIndexFlags Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
variable {G : Type*} [Group G]

theorem Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.inf_relIndex_of_le (H N L : Subgroup G) (hL : L ≤ N) :
    (H ⊓ N).relIndex L = H.relIndex L := by sorry
