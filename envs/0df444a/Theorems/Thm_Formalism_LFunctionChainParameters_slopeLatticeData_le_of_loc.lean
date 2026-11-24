-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_le_of_loc
-- name    : Formalism.LFunctionChainParameters.slopeLatticeData.le_of_loc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:16.470357+00:00
-- url     : https://prove2.me/theorems/e2b7621f-bb2a-485d-ac86-3221894b8e5e
-- title:
--   slope Lattice Data: le of loc
-- statement:
--   The slope Lattice Data construction uses the le of loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L1049-L1075
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ExistsNsmulMem.lean#L1049-L1075

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
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
omit [Module K V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.LFunctionChainParameters.slopeLatticeData.le_of_loc [∀ w : FinPl K, Module (Rloc w) V]
    [∀ w : FinPl K, IsScalarTower (𝓞 K) (Rloc w) V] {A B : Submodule (𝓞 K) V}
    (h : ∀ w : FinPl K, Submodule.span (Rloc w) (A : Set V) ≤ Submodule.span (Rloc w) (B : Set V)) :
    A ≤ B := by sorry
