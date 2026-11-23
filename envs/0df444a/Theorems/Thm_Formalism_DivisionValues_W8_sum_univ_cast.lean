-- Prove2me | Theorems.Thm_Formalism_DivisionValues_W8_sum_univ_cast
-- name    : Formalism.DivisionValues.W8.sum_univ_cast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:27:19.424797+00:00
-- url     : https://prove2.me/theorems/77d64d55-3629-4fc7-96e3-1ec1327982de
-- title:
--   W8: sum univ cast
-- statement:
--   The W8 construction uses the sum univ cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramHook.lean#L187-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramHook.lean#L187-L190

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
open Formalism.DivisionValues.W8

theorem Formalism.DivisionValues.W8.sum_univ_cast {n : ℕ} (g : Fin n → ℕ) :
    (((Finset.univ.val.map g).sum : ℕ) : ℝ) = ∑ i, (g i : ℝ) := by sorry
