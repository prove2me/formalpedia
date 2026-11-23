-- Prove2me | Theorems.Thm_Formalism_DivisionValues_W8_pair_abs
-- name    : Formalism.DivisionValues.W8.pair_abs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:22:54.432853+00:00
-- url     : https://prove2.me/theorems/eda5507c-36d2-461f-962f-6499866e50a7
-- title:
--   W8: pair abs
-- statement:
--   The W8 construction uses the pair abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramHook.lean#L85-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramHook.lean#L85-L107

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

theorem Formalism.DivisionValues.W8.pair_abs {La d : ℝ} (y y' : ℕ) (hy : Real.log (y : ℝ) ≤ La) (hLa : 1 ≤ La)
    (hd : |(y : ℝ) - (y' : ℝ)| ≤ d) : ph (y : ℝ) - ph (y' : ℝ) ≤ d * La := by sorry
