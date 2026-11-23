-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_muMaxDef_le
-- name    : Formalism.LFunctionChainParameters.slopeLatticeData.muMaxDef_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:26.654431+00:00
-- url     : https://prove2.me/theorems/e9a4d229-b24e-437c-bbcd-7b4048a7de4f
-- title:
--   slope Lattice Data: mu Max Def le
-- statement:
--   The slope Lattice Data construction uses the mu Max Def le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L353-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L353-L365

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
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]

theorem Formalism.LFunctionChainParameters.slopeLatticeData.muMaxDef_le (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    {L : Submodule (𝓞 K) V} (hL0 : L ≠ ⊥) {B : ℝ}
    (h : ∀ Q : Submodule (𝓞 K) V, Q ≤ L → Q ≠ ⊥ → muDef b X Q ≤ B) : muMaxDef b X L ≤ B := by sorry
