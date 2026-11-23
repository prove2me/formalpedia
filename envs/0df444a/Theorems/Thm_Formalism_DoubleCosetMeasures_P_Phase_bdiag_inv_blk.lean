-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_bdiag_inv_blk
-- name    : Formalism.DoubleCosetMeasures.P.Phase.bdiag_inv_blk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:00.650844+00:00
-- url     : https://prove2.me/theorems/ff93f412-e707-4de9-943c-c6b7bfbb2192
-- title:
--   Phase: bdiag inv blk
-- statement:
--   The Phase construction uses the bdiag inv blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L436-L455
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L436-L455

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
variable {K : Type} [CommRing K]

theorem Formalism.DoubleCosetMeasures.P.Phase.bdiag_inv_blk (s : List ℕ) {x : Matrix (Fin s.sum) (Fin s.sum) K} (hx : IsLowUni x)
    {a c : Fin s.sum} (h : blk s a ≠ blk s c) : (bdiag s x)⁻¹ a c = 0 := by sorry
