-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_inv_cancel
-- name    : Formalism.LFunctionChainParameters.slopeLatticeData.idealSmul_inv_cancel
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:29.790376+00:00
-- url     : https://prove2.me/theorems/2630b28e-9099-46b7-9206-8f7e36200214
-- title:
--   slope Lattice Data: ideal Smul inv cancel
-- statement:
--   The slope Lattice Data construction uses the ideal Smul inv cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L117-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L117-L122

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
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.LFunctionChainParameters.slopeLatticeData.idealSmul_inv_cancel {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : I ≠ 0)
    (L : Submodule (𝓞 K) V) :
    idealSmul ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K)
      (idealSmul (I : Submodule (𝓞 K) K) L) = L := by sorry
