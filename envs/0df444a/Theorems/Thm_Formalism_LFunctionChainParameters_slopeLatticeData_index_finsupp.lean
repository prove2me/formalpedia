-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_index_finsupp
-- name    : Formalism.LFunctionChainParameters.slopeLatticeData.index_finsupp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:59:14.15384+00:00
-- url     : https://prove2.me/theorems/c67fa370-2118-4871-ac8f-546f49a4cfc2
-- title:
--   slope Lattice Data: index finsupp
-- statement:
--   The slope Lattice Data construction uses the index finsupp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L616-L627
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L616-L627

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

theorem Formalism.LFunctionChainParameters.slopeLatticeData.index_finsupp {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (A B : Submodule (𝓞 K) V) (h : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0) :
    ∃ k : FinPl K →₀ ℕ, (∀ w : FinPl K, lenAt w A B = (k w : ℕ∞)) ∧
      B.toAddSubgroup.relIndex A.toAddSubgroup = k.prod fun w j => Ideal.absNorm w.1 ^ j := by sorry
