-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_WeightedMeanLemmas_wmean_sub
-- name    : Formalism.LFunctionChainParameters.WeightedMeanLemmas.wmean_sub
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T09:49:20.231258+00:00
-- url     : https://prove2.me/theorems/37fa0070-ac67-437a-bfe6-4d9b57db62a4
-- title:
--   Weighted Mean Lemmas: wmean sub
-- statement:
--   The Weighted Mean Lemmas construction uses the wmean sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/WeightedMeanLemmaNeedsDegree.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/WeightedMeanLemmaNeedsDegree.lean#L35-L39

import Definitions.Def_Formalism_SizeWindowBrackets_RealSlopeBoundsSplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.WeightedMeanLemmas
open Finset
variable {ι : Type*} [Fintype ι]

theorem Formalism.LFunctionChainParameters.WeightedMeanLemmas.wmean_sub (d X Y : ι → ℝ) :
    wmean d (fun u => X u - Y u) = wmean d X - wmean d Y := by sorry
