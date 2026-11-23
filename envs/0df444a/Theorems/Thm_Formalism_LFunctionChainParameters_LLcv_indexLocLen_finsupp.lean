-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_indexLocLen_finsupp
-- name    : Formalism.LFunctionChainParameters.LLcv.indexLocLen_finsupp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:31:13.972101+00:00
-- url     : https://prove2.me/theorems/b8d5d5bf-b842-49f6-b34d-fcd4d4497628
-- title:
--   LLcv: index Loc Len finsupp
-- statement:
--   The LLcv construction uses the index Loc Len finsupp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TruncatedLatticeHolds.lean#L189-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TruncatedLatticeHolds.lean#L189-L205

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

theorem Formalism.LFunctionChainParameters.LLcv.indexLocLen_finsupp {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module (𝓞 K) V] (A B : Submodule (𝓞 K) V) (hBA : B ≤ A)
    (h : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0) :
    ∃ k : {p : Ideal (𝓞 K) // p.IsMaximal} →₀ ℕ,
      (∀ w : {p : Ideal (𝓞 K) // p.IsMaximal},
        (haveI := w.2.isPrime; pLen w.1 A B) = (k w : ℕ∞)) ∧
      Real.log (B.toAddSubgroup.relIndex A.toAddSubgroup : ℝ) =
        ∑ w ∈ k.support, Real.log (Ideal.absNorm w.1 : ℝ) * (k w : ℝ) := by sorry
