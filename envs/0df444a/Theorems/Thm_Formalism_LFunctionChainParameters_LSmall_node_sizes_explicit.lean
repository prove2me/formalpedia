-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LSmall_node_sizes_explicit
-- name    : Formalism.LFunctionChainParameters.LSmall.node_sizes_explicit
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:56:12.474029+00:00
-- url     : https://prove2.me/theorems/d2cb8720-aad1-4cc6-8ab7-faf5797dfe1f
-- title:
--   LSmall: node sizes explicit
-- statement:
--   The LSmall construction uses the node sizes explicit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PSmall.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PSmall.lean#L57-L60

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

theorem Formalism.LFunctionChainParameters.LSmall.node_sizes_explicit : NodeSizesText := by sorry
