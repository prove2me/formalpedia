-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_Filt_sub_bot
-- name    : Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.sub_bot
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:55:52.392222+00:00
-- url     : https://prove2.me/theorems/e9a780a7-d7dc-4792-9675-2770249322f2
-- title:
--   Filt: sub bot
-- statement:
--   The Filt construction uses the sub bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RelativeIndexFlags/RelIndexUnipotentConjSymm.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RelativeIndexFlags/RelIndexUnipotentConjSymm.lean#L26-L31

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_InvSubOneBd
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_FiltRelIndex
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_RelIndexUnipotentConjSymm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RelativeIndexFlags Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
variable {n : ℕ} {K : Type*} [Field K] (L : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))

theorem Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.sub_bot : (FG n K n).subgroupOf L = ⊥ := by sorry
