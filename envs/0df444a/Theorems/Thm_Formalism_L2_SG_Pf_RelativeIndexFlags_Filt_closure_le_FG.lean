-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_Filt_closure_le_FG
-- name    : Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.closure_le_FG
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:54:37.681477+00:00
-- url     : https://prove2.me/theorems/b8a67a90-4105-4b51-b5bb-6cc6d08a518d
-- title:
--   Filt: closure le FG
-- statement:
--   The Filt construction uses the closure le FG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RelativeIndexFlags/InvSubOneBd.lean#L147-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RelativeIndexFlags/InvSubOneBd.lean#L147-L160

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

theorem Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.closure_le_FG :
    Subgroup.closure {a : Matrix.GeneralLinearGroup (Fin n) K |
      ∀ i j, (i < j → (a : Matrix (Fin n) (Fin n) K) i j = 0) ∧
        (i = j → (a : Matrix (Fin n) (Fin n) K) i j = 1)} ≤ FG n K 0 := by sorry
