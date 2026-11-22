-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_mem_idealSmul
-- name    : Formalism.LFunctionChainParameters.slopeLatticeData.mem_idealSmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:28.632379+00:00
-- url     : https://prove2.me/theorems/36e12e89-52d9-46c8-8d15-9cf7e9f71070
-- title:
--   slope Lattice Data: mem ideal Smul
-- statement:
--   The slope Lattice Data construction uses the mem ideal Smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L26-L28

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
omit [IsScalarTower (𝓞 K) K V]

theorem Formalism.LFunctionChainParameters.slopeLatticeData.mem_idealSmul {I : Submodule (𝓞 K) K} {L : Submodule (𝓞 K) V} {a : K} {x : V}
    (ha : a ∈ I) (hx : x ∈ L) : a • x ∈ idealSmul I L := by sorry
