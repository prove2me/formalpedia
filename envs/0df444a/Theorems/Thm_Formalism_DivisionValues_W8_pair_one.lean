-- Prove2me | Theorems.Thm_Formalism_DivisionValues_W8_pair_one
-- name    : Formalism.DivisionValues.W8.pair_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:24:42.275929+00:00
-- url     : https://prove2.me/theorems/bc5bda21-826e-589a-8e01-da77e3033337
-- title:
--   W8: pair one
-- statement:
--   The W8 construction uses the pair one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramHook.lean#L67-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramHook.lean#L67-L83

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

theorem Formalism.DivisionValues.W8.pair_one {La d : ℝ} (y y' : ℕ) (hy : Real.log (y : ℝ) ≤ La) (hLa : 1 ≤ La) (hd0 : 0 ≤ d)
    (hd : (y : ℝ) - (y' : ℝ) ≤ d) : ph (y : ℝ) - ph (y' : ℝ) ≤ d * La + 1 := by sorry
