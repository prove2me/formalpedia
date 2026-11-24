-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_le_span_loc
-- name    : Formalism.LFunctionChainParameters.slopeLatticeData.idealSmul_le_span_loc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:28.486236+00:00
-- url     : https://prove2.me/theorems/cc266c6c-2996-4adb-9351-af20daad4124
-- title:
--   slope Lattice Data: ideal Smul le span loc
-- statement:
--   The slope Lattice Data construction uses the ideal Smul le span loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L979-L999
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L979-L999

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
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.LFunctionChainParameters.slopeLatticeData.idealSmul_le_span_loc (w : Ideal (𝓞 K)) [w.IsPrime] [Module (Localization.AtPrime w) V]
    [IsScalarTower (𝓞 K) (Localization.AtPrime w) V] {J : FI} (hJ : HalfUnit w J)
    (L : Submodule (𝓞 K) V) :
    idealSmul (J : Submodule (𝓞 K) K) L ≤
      (Submodule.span (Localization.AtPrime w) (L : Set V)).restrictScalars (𝓞 K) := by sorry
