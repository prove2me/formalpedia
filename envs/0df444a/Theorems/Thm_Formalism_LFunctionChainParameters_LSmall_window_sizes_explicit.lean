-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LSmall_window_sizes_explicit
-- name    : Formalism.LFunctionChainParameters.LSmall.window_sizes_explicit
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:56:01.009078+00:00
-- url     : https://prove2.me/theorems/cb7f0052-e4cb-41ca-a85a-d3df99be864f
-- title:
--   LSmall: window sizes explicit
-- statement:
--   The LSmall construction uses the window sizes explicit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PSmall.lean#L39-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PSmall.lean#L39-L55

import Definitions.Def_Formalism_SizeWindowBrackets_SSmall
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PSmall
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
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LSmall
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds

theorem Formalism.LFunctionChainParameters.LSmall.window_sizes_explicit : WindowSizesText := by sorry
