-- Prove2me | Theorems.Thm_Formalism_DivisionValues_W8_off_nonneg
-- name    : Formalism.DivisionValues.W8.off_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:22:36.523193+00:00
-- url     : https://prove2.me/theorems/cb670cf6-4cfe-45cf-a7ba-f6fe56aa4614
-- title:
--   W8: off nonneg
-- statement:
--   The W8 construction uses the off nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramHook.lean#L480-L483
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramHook.lean#L480-L483

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

theorem Formalism.DivisionValues.W8.off_nonneg {n w : ℕ} {S Bl sh : ℝ} {ν ap : Multiset ℕ} (h : IsRowsOff n w S Bl sh ν ap) :
    0 ≤ S ∧ 0 ≤ Bl := by sorry
