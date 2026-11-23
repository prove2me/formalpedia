-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_lt_of_lt_of_ne
-- name    : Formalism.DoubleCosetMeasures.P.Phase.blk_lt_of_lt_of_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:45:03.721413+00:00
-- url     : https://prove2.me/theorems/c72dfab1-8464-4fdd-849b-243ba66a4c1b
-- title:
--   Phase: blk lt of lt of ne
-- statement:
--   The Phase construction uses the blk lt of lt of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L109-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L109-L110

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

theorem Formalism.DoubleCosetMeasures.P.Phase.blk_lt_of_lt_of_ne (s : List ℕ) {a c : Fin s.sum} (h : a < c) (hb : blk s a ≠ blk s c) :
    blk s a < blk s c := by sorry
