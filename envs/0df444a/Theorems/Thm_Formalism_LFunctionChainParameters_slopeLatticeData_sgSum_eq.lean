-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_sgSum_eq
-- name    : Formalism.LFunctionChainParameters.slopeLatticeData.sgSum_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T09:50:30.744262+00:00
-- url     : https://prove2.me/theorems/8ba3e37a-5105-4a89-83c0-481c5992ac76
-- title:
--   slope Lattice Data: sg Sum eq
-- statement:
--   The slope Lattice Data construction uses the sg Sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L432-L445
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L432-L445

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

theorem Formalism.LFunctionChainParameters.slopeLatticeData.sgSum_eq (σ τ : FinPl K →₀ ℤ) :
    sgSum σ τ = -(2 * Real.log ((FractionalIdeal.absNorm (idealPow (-σ)) : ℚ) : ℝ) /
        (Module.finrank ℚ K : ℝ)) -
      2 * Real.log ((FractionalIdeal.absNorm (idealPow τ) : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) := by sorry
