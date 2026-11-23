-- Prove2me | Theorems.Thm_Formalism_DivisionValues_W8_arith_nN
-- name    : Formalism.DivisionValues.W8.arith_nN
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:05:27.984797+00:00
-- url     : https://prove2.me/theorems/2456b57d-4764-4335-8f3b-40677fc55ca8
-- title:
--   W8: arith n N
-- statement:
--   The W8 construction uses the arith n N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramHook.lean#L426-L430
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramHook.lean#L426-L430

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRows
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Definitions.Def_Formalism_LogFactorialIndices_SubspaceIndexSigned
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.LatticeIndexTer (ph)
open W8
open Formalism.DivisionValues.W8

theorem Formalism.DivisionValues.W8.arith_nN {n k N cs : ℝ} (hn : 0 ≤ n) (hnk : n ≤ k) (hkN : k ≤ N) (hcs : 0 ≤ cs) :
    n * (cs * N) ≤ cs * N ^ 2 := by sorry
