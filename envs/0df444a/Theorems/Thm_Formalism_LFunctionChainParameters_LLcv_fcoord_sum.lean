-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_fcoord_sum
-- name    : Formalism.LFunctionChainParameters.LLcv.fcoord_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:38:16.66112+00:00
-- url     : https://prove2.me/theorems/aa266c73-035f-41a4-b92c-58f2ccaeef2b
-- title:
--   LLcv: fcoord sum
-- statement:
--   The LLcv construction uses the fcoord sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TruncatedLatticeHolds.lean#L594-L602
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TruncatedLatticeHolds.lean#L594-L602

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
open scoped Matrix
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

theorem Formalism.LFunctionChainParameters.LLcv.fcoord_sum (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    {j : ℕ} (c : Fin j → K) (e : Fin j → V) :
    fcoord b X v (∑ k, c k • e k) = ∑ k, v.embedding (c k) • fcoord b X v (e k) := by sorry
