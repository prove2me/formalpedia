-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LChain6_Chi8_tm_eval
-- name    : Formalism.LFunctionChainParameters.LChain6.Chi8.tm_eval
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:45.395452+00:00
-- url     : https://prove2.me/theorems/474e3050-6ec0-4a56-9bf1-8d3213283f49
-- title:
--   Chi8: tm eval
-- statement:
--   The Chi8 construction uses the tm eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ChiEightNoRealZeroHypothesis.lean#L52-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ChiEightNoRealZeroHypothesis.lean#L52-L58

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_DzDifferentiableOn
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesFromSizeAndCount
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChiEightNoRealZeroHypothesis
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
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain6 Formalism.LFunctionChainParameters.LChain6.Chi8
open Formalism.ZF.ComplexPowerDifferenceIntegral

theorem Formalism.LFunctionChainParameters.LChain6.Chi8.tm_eval (s : ℂ) (m r : ℕ) (hr : 0 < r) :
    tm s (m * 8 + r) = chi ((r : ℕ) : ZMod 8) * ((8 * (m : ℝ) + (r : ℝ) : ℝ) : ℂ) ^ (-s) := by sorry
