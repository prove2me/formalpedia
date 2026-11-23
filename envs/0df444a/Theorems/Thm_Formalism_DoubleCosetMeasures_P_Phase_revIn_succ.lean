-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revIn_succ
-- name    : Formalism.DoubleCosetMeasures.P.Phase.revIn_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:12.952809+00:00
-- url     : https://prove2.me/theorems/9cb2a426-739c-4833-90dc-93d183440b18
-- title:
--   Phase: rev In succ
-- statement:
--   The Phase construction uses the rev In succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L70-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L70-L83

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

theorem Formalism.DoubleCosetMeasures.P.Phase.revIn_succ : ∀ (s : List ℕ) (j : ℕ), j + 1 < s.sum → blk s j = blk s (j + 1) →
    revIn s (j + 1) + 1 = revIn s j
  := by sorry
