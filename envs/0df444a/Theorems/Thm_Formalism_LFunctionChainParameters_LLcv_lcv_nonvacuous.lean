-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_lcv_nonvacuous
-- name    : Formalism.LFunctionChainParameters.LLcv.lcv_nonvacuous
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:50:46.124836+00:00
-- url     : https://prove2.me/theorems/56a099f5-8891-4f20-9767-5ca25e0867b3
-- title:
--   LLcv: lcv nonvacuous
-- statement:
--   The LLcv construction uses the lcv nonvacuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TruncatedLatticeHolds.lean#L729-L761
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TruncatedLatticeHolds.lean#L729-L761

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

theorem Formalism.LFunctionChainParameters.LLcv.lcv_nonvacuous :
    letI : StarRing (CyclotomicField 3 ℚ) := starRingOfComm
    0 < lcvFin (K := CyclotomicField 3 ℚ) (V := CyclotomicField 3 ℚ) (fun _ : Fin 1 => 1)
      (idealSmul ((FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 (CyclotomicField 3 ℚ)))
        (2 : CyclotomicField 3 ℚ) : FractionalIdeal (nonZeroDivisors (𝓞 (CyclotomicField 3 ℚ)))
          (CyclotomicField 3 ℚ)) : Submodule (𝓞 (CyclotomicField 3 ℚ)) (CyclotomicField 3 ℚ))
        (Submodule.span (𝓞 (CyclotomicField 3 ℚ)) (Set.range fun _ : Fin 1 => 1))) := by sorry
