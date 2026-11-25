-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_slope_local_nonvacuous
-- name    : Formalism.LFunctionChainParameters.slopeLatticeData.slope_local_nonvacuous
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:58:01.298424+00:00
-- url     : https://prove2.me/theorems/a6701e64-a132-54ea-adf7-e5e34f53290c
-- title:
--   slope Lattice Data: slope local nonvacuous
-- statement:
--   The slope Lattice Data construction uses the slope local nonvacuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L1124-L1150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L1124-L1150

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

theorem Formalism.LFunctionChainParameters.slopeLatticeData.slope_local_nonvacuous {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (σ τ : FinPl K →₀ ℤ)
    (M : Submodule (𝓞 K) V) :
    ∃ (_ : ∀ w : FinPl K, Module (Rloc w) V) (_ : ∀ w : FinPl K, IsScalarTower (𝓞 K) (Rloc w) V)
      (ϖ : FinPl K → 𝓞 K) (N N' : Submodule (𝓞 K) V), (∀ w, ϖ w ∈ w.1 ∧ ϖ w ∉ w.1 ^ 2) ∧
      rkK N = rkK M ∧
      (∀ w, locScal w 1 N ≤ locScal w (algebraMap (𝓞 K) K (ϖ w) ^ τ w) M) ∧
      (∀ w, locScal w 1 N' = locScal w (algebraMap (𝓞 K) K (ϖ w) ^ (-σ w)) N) := by sorry
