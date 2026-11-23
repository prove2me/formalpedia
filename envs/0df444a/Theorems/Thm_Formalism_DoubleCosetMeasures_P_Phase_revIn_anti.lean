-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revIn_anti
-- name    : Formalism.DoubleCosetMeasures.P.Phase.revIn_anti
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:15.905212+00:00
-- url     : https://prove2.me/theorems/2c6987f8-a220-40f6-b657-e58c096c6f72
-- title:
--   Phase: rev In anti
-- statement:
--   The Phase construction uses the rev In anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L57-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L57-L68

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
open Formalism.DoubleCosetMeasures.P.Phase

theorem Formalism.DoubleCosetMeasures.P.Phase.revIn_anti : ∀ (s : List ℕ) (i j : ℕ), j < s.sum → i < j → blk s i = blk s j →
    revIn s j < revIn s i
  := by sorry
