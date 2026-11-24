-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_rk_fractional
-- name    : Formalism.LFunctionChainParameters.LLcv.rk_fractional
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:13.406168+00:00
-- url     : https://prove2.me/theorems/e5f54514-9760-479c-b6ea-f3d253b6c00c
-- title:
--   LLcv: rk fractional
-- statement:
--   The LLcv construction uses the rk fractional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TruncatedLatticeHolds.lean#L450-L454
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TruncatedLatticeHolds.lean#L450-L454

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

theorem Formalism.LFunctionChainParameters.LLcv.rk_fractional (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {N : Submodule (𝓞 K) V} (hN : N.FG) {I : FI} (hI : I ≠ 0) :
    rk (realize b X) (idealSmul (I : Submodule (𝓞 K) K) N) = rk (realize b X) N := by sorry
