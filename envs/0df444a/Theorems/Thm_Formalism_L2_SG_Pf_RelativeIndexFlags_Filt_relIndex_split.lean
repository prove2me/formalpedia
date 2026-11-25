-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_Filt_relIndex_split
-- name    : Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.relIndex_split
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:45:06.548908+00:00
-- url     : https://prove2.me/theorems/660ecc63-83e6-4699-9263-2250a372dc00
-- title:
--   Filt: rel Index split
-- statement:
--   The Filt construction uses the rel Index split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RelativeIndexFlags/RelIndexEqIndexOfMul.lean#L50-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RelativeIndexFlags/RelIndexEqIndexOfMul.lean#L50-L69

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

theorem Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.relIndex_split (N : Subgroup G) [hN : N.Normal] (H X : Subgroup G) (hHX : H ≤ X) :
    H.relIndex X = (H ⊓ N).relIndex (X ⊓ N) * (H ⊔ N).relIndex (X ⊔ N) := by sorry
