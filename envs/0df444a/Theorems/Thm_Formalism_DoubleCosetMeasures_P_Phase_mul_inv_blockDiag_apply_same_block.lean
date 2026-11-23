-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_mul_inv_blockDiag_apply_same_block
-- name    : Formalism.DoubleCosetMeasures.P.Phase.mul_inv_blockDiag_apply_same_block
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:06.018167+00:00
-- url     : https://prove2.me/theorems/8320394f-960b-4df2-b60b-0be5e6e42876
-- title:
--   Phase: mul inv block Diag apply same block
-- statement:
--   The Phase construction uses the mul inv block Diag apply same block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L457-L465
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MulInvBlockDiagApplySameBlock.lean#L457-L465

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

theorem Formalism.DoubleCosetMeasures.P.Phase.mul_inv_blockDiag_apply_same_block (s : List ℕ) {x : Matrix (Fin s.sum) (Fin s.sum) K} (hx : IsLowUni x)
    {a c : Fin s.sum} (hac : blk s a = blk s c) :
    (x * (bdiag s x)⁻¹) a c = (1 : Matrix (Fin s.sum) (Fin s.sum) K) a c := by sorry
