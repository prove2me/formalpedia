-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_span_loc_idealSmul
-- name    : Formalism.LFunctionChainParameters.slopeLatticeData.span_loc_idealSmul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:32.78202+00:00
-- url     : https://prove2.me/theorems/9d43b600-2e66-4152-a19b-9cb1a6ab54b0
-- title:
--   slope Lattice Data: span loc ideal Smul
-- statement:
--   The slope Lattice Data construction uses the span loc ideal Smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L1001-L1012
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L1001-L1012

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

theorem Formalism.LFunctionChainParameters.slopeLatticeData.span_loc_idealSmul (w : Ideal (𝓞 K)) [w.IsPrime] [Module (Localization.AtPrime w) V]
    [IsScalarTower (𝓞 K) (Localization.AtPrime w) V] {J : FI} (hJ : WUnit w J)
    (L : Submodule (𝓞 K) V) :
    Submodule.span (Localization.AtPrime w)
      ((idealSmul (J : Submodule (𝓞 K) K) L : Submodule (𝓞 K) V) : Set V) =
      Submodule.span (Localization.AtPrime w) (L : Set V) := by sorry
