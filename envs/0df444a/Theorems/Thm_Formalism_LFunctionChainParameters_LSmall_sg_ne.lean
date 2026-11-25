-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LSmall_sg_ne
-- name    : Formalism.LFunctionChainParameters.LSmall.sg_ne
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:51:36.531131+00:00
-- url     : https://prove2.me/theorems/a7182074-4b70-4838-b7ea-7c10e5307704
-- title:
--   LSmall: sg ne
-- statement:
--   The LSmall construction uses the sg ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PSmall.lean#L99-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PSmall.lean#L99-L102

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
open Formalism.LFunctionChainParameters.LHost
open Formalism.FrobeniusOrbits (HostHyp HGrp hcl)

theorem Formalism.LFunctionChainParameters.LSmall.sg_ne {H : Type} [AddCommGroup H] : (0 : E0 × H) ≠ sg := by sorry
