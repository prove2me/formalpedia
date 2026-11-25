-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LSmall_cj_apply
-- name    : Formalism.LFunctionChainParameters.LSmall.cj_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:54:38.336382+00:00
-- url     : https://prove2.me/theorems/69aceffd-310d-440c-b551-c7ca81aa3966
-- title:
--   LSmall: cj apply
-- statement:
--   The LSmall construction uses the cj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PSmall.lean#L71-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PSmall.lean#L71-L71

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

theorem Formalism.LFunctionChainParameters.LSmall.cj_apply {m n : Type} (M : Matrix m n ℂ) (i : m) (j : n) : cj M i j = starRingEnd ℂ (M i j) := by sorry
