-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_Filt_FG_eq_one
-- name    : Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.FG_eq_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:44:47.63706+00:00
-- url     : https://prove2.me/theorems/9e54074c-34e3-45cd-a821-59308fad79b6
-- title:
--   Filt: FG eq one
-- statement:
--   The Filt construction uses the FG eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RelativeIndexFlags/InvSubOneBd.lean#L104-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RelativeIndexFlags/InvSubOneBd.lean#L104-L108

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_InvSubOneBd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RelativeIndexFlags Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
variable {n : ℕ} {K : Type*} [Field K]

theorem Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.FG_eq_one {a : Matrix.GeneralLinearGroup (Fin n) K} (ha : a ∈ FG n K n) : a = 1 := by sorry
