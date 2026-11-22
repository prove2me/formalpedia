-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_finPl_coe_ne_zero
-- name    : Formalism.LFunctionChainParameters.slopeLatticeData.finPl_coe_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:58.276508+00:00
-- url     : https://prove2.me/theorems/9df89630-31b4-4198-a4e2-685db5c298b0
-- title:
--   slope Lattice Data: fin Pl coe ne zero
-- statement:
--   The slope Lattice Data construction uses the fin Pl coe ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L407-L409
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L407-L409

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

theorem Formalism.LFunctionChainParameters.slopeLatticeData.finPl_coe_ne_zero (w : FinPl K) :
    (w.1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := by sorry
