-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_spanSingleton_zpow
-- name    : Formalism.LFunctionChainParameters.slopeLatticeData.spanSingleton_zpow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T09:50:23.134796+00:00
-- url     : https://prove2.me/theorems/8e52015a-353b-482c-8f55-b647ce976075
-- title:
--   slope Lattice Data: span Singleton zpow
-- statement:
--   The slope Lattice Data construction uses the span Singleton zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L969-L975
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L969-L975

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.slopeLatticeData
open Formalism.HN Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K]
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K

theorem Formalism.LFunctionChainParameters.slopeLatticeData.spanSingleton_zpow (x : K) (k : ℤ) :
    (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x : FI) ^ k =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (x ^ k) := by sorry
