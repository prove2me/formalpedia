-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_lt_of_blk_eq
-- name    : Formalism.DoubleCosetMeasures.P.Phase.revF_lt_of_blk_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:26:59.709923+00:00
-- url     : https://prove2.me/theorems/bceca985-c8d3-4c15-a0ce-6ff7be2596bf
-- title:
--   Phase: rev F lt of blk eq
-- statement:
--   The Phase construction uses the rev F lt of blk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L98-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L98-L99

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

theorem Formalism.DoubleCosetMeasures.P.Phase.revF_lt_of_blk_eq (s : List ℕ) {a c : Fin s.sum} (hb : blk s a = blk s c) (h : a < c) :
    revF s c < revF s a := by sorry
