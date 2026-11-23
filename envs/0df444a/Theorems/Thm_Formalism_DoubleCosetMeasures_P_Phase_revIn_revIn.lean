-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revIn_revIn
-- name    : Formalism.DoubleCosetMeasures.P.Phase.revIn_revIn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:57.997458+00:00
-- url     : https://prove2.me/theorems/1e89c2c0-0f76-42ca-9d06-f7d2bd7ae844
-- title:
--   Phase: rev In rev In
-- statement:
--   The Phase construction uses the rev In rev In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L23-L33

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

theorem Formalism.DoubleCosetMeasures.P.Phase.revIn_revIn : ∀ (s : List ℕ) (j : ℕ), j < s.sum → revIn s (revIn s j) = j
  := by sorry
