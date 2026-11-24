-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_span_inf
-- name    : Formalism.LFunctionChainParameters.LLcv.span_inf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:26.192162+00:00
-- url     : https://prove2.me/theorems/2c478271-8f3e-486d-bdcf-660aeff1b0a0
-- title:
--   LLcv: span inf
-- statement:
--   The LLcv construction uses the span inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TruncatedLatticeHolds.lean#L264-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TruncatedLatticeHolds.lean#L264-L278

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
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
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LLcv
open Formalism.HN Formalism.HermitianLatticesTheory Formalism.LFunctionChainParameters.slopeLatticeData
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.LFunctionChainParameters.LLcv.span_inf {E M : Submodule (𝓞 K) V} (hE : E.FG)
    (h : Submodule.span K (E : Set V) = Submodule.span K (M : Set V)) :
    Submodule.span K ((E ⊓ M : Submodule (𝓞 K) V) : Set V) = Submodule.span K (E : Set V) := by sorry
