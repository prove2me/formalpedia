-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LSmall_node_sizes_of_windows
-- name    : Formalism.LFunctionChainParameters.LSmall.node_sizes_of_windows
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:55:45.351995+00:00
-- url     : https://prove2.me/theorems/e08c2df2-0aa6-4859-a3d1-ca336d6e654d
-- title:
--   LSmall: node sizes of windows
-- statement:
--   The LSmall construction uses the node sizes of windows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PSmall.lean#L15-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PSmall.lean#L15-L35

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
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem Formalism.LFunctionChainParameters.LSmall.node_sizes_of_windows : NodeSizesOfWindows (H := H) := by sorry
