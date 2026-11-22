-- Prove2me | Theorems.Thm_Formalism_FX_l_function_partial_sum
-- name    : Formalism.FX.l_function_partial_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:43:56.672782+00:00
-- url     : https://prove2.me/theorems/74f0f615-3d43-4dea-8674-be2dcd8f3398
-- title:
--   FX: l function partial sum
-- statement:
--   The FX construction uses the l function partial sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LPartialSum.lean#L136-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LPartialSum.lean#L136-L169

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LPartialSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.FX
open LFunctionPartialSum

theorem Formalism.FX.l_function_partial_sum : LPartialSum := by sorry
