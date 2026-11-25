-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_muMin_fractional
-- name    : Formalism.LFunctionChainParameters.LLcv.muMin_fractional
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T09:49:56.393041+00:00
-- url     : https://prove2.me/theorems/1ee839d7-3b89-4e88-88d9-1b4f4329dc7a
-- title:
--   LLcv: mu Min fractional
-- statement:
--   The LLcv construction uses the mu Min fractional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TruncatedLatticeHolds.lean#L489-L504
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TruncatedLatticeHolds.lean#L489-L504

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
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K

theorem Formalism.LFunctionChainParameters.LLcv.muMin_fractional (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {L : Submodule (𝓞 K) V} (hL : L.FG) (hL0 : L ≠ ⊥) {I : FI}
    (hI : I ≠ 0) :
    muMin (realize b X) (idealSmul (I : Submodule (𝓞 K) K) L) = muMin (realize b X) L -
      Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) := by sorry
