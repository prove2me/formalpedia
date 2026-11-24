-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_wUnit_idealPow
-- name    : Formalism.LFunctionChainParameters.slopeLatticeData.wUnit_idealPow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:04.610834+00:00
-- url     : https://prove2.me/theorems/2b0072c5-a83c-493b-a0c6-a94c94c3dec3
-- title:
--   slope Lattice Data: w Unit ideal Pow
-- statement:
--   The slope Lattice Data construction uses the w Unit ideal Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L935-L967
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L935-L967

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

theorem Formalism.LFunctionChainParameters.slopeLatticeData.wUnit_idealPow (w : FinPl K) {ϖ : 𝓞 K} (h1 : ϖ ∈ w.1) (h2 : ϖ ∉ w.1 ^ 2)
    (n : FinPl K →₀ ℤ) : WUnit w.1 (idealPow n *
      ((FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap (𝓞 K) K ϖ) : FI) ^
        (n w))⁻¹) := by sorry
