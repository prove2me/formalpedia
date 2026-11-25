-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LSmall_cj_sub
-- name    : Formalism.LFunctionChainParameters.LSmall.cj_sub
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:51:58.299042+00:00
-- url     : https://prove2.me/theorems/7de613e9-8b3e-4dd7-ac08-358f61428296
-- title:
--   LSmall: cj sub
-- statement:
--   The LSmall construction uses the cj sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PSmall.lean#L76-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PSmall.lean#L76-L77

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
open Matrix Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare

theorem Formalism.LFunctionChainParameters.LSmall.cj_sub {m n : Type} (M N : Matrix m n ℂ) : cj (M - N) = cj M - cj N := by sorry
