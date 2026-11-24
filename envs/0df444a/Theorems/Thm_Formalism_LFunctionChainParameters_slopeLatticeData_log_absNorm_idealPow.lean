-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_log_absNorm_idealPow
-- name    : Formalism.LFunctionChainParameters.slopeLatticeData.log_absNorm_idealPow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T09:50:28.212523+00:00
-- url     : https://prove2.me/theorems/c57ec3e0-2d58-4c41-b43f-a8ef036bc92f
-- title:
--   slope Lattice Data: log abs Norm ideal Pow
-- statement:
--   The slope Lattice Data construction uses the log abs Norm ideal Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L415-L430
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L415-L430

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

theorem Formalism.LFunctionChainParameters.slopeLatticeData.log_absNorm_idealPow (n : FinPl K →₀ ℤ) (U : Finset (FinPl K)) (hU : n.support ⊆ U) :
    Real.log ((FractionalIdeal.absNorm (idealPow n) : ℚ) : ℝ) =
      ∑ w ∈ U, (n w : ℝ) * Real.log (Ideal.absNorm w.1 : ℝ) := by sorry
