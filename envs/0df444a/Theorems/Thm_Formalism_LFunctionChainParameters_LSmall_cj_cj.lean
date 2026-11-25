-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LSmall_cj_cj
-- name    : Formalism.LFunctionChainParameters.LSmall.cj_cj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:52:15.689602+00:00
-- url     : https://prove2.me/theorems/ae422e18-3c4c-4632-adca-5b1af6b931a9
-- title:
--   LSmall: cj cj
-- statement:
--   The LSmall construction uses the cj cj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PSmall.lean#L73-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PSmall.lean#L73-L74

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

theorem Formalism.LFunctionChainParameters.LSmall.cj_cj {m n : Type} (M : Matrix m n ℂ) : cj (cj M) = M := by sorry
