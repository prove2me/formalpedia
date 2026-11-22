-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revIn
-- name    : Formalism.DoubleCosetMeasures.P.Phase.blk_revIn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:40.960638+00:00
-- url     : https://prove2.me/theorems/4c2f58f6-1e1b-4159-83b4-525372ca67cd
-- title:
--   Phase: blk rev In
-- statement:
--   The Phase construction uses the blk rev In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L35-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L35-L45

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

theorem Formalism.DoubleCosetMeasures.P.Phase.blk_revIn : ∀ (s : List ℕ) (j : ℕ), j < s.sum → blk s (revIn s j) = blk s j
  := by sorry
