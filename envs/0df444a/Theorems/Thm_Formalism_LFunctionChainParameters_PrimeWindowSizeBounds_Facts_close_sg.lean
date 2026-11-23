-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_close_sg
-- name    : Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts.close_sg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:01:23.696208+00:00
-- url     : https://prove2.me/theorems/726522ed-45b7-494f-9cee-dbae91f841ac
-- title:
--   Facts: close sg
-- statement:
--   The Facts construction uses the close sg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L323-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L323-L327

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr
open Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts
variable {P : Par} {e K z u E X S sb v w8 : ℝ} (F : Facts P e K z u E X S sb v w8)
include F

theorem Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.Facts.close_sg {c w : ℝ} (_hc0 : 0 ≤ c) (hc : c ≤ 1) (hw0 : 0 ≤ w) (hw : w ≤ sg P K) :
    P.b * c * w ≤ sg P K * P.b := by sorry
