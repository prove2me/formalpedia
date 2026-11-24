-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_ht_lidx
-- name    : Formalism.LFunctionChainParameters.LLcv.ht_lidx
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:24.700582+00:00
-- url     : https://prove2.me/theorems/334767eb-079e-4f42-94ae-59781a1bae96
-- title:
--   LLcv: ht lidx
-- statement:
--   The LLcv construction uses the ht lidx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TruncatedLatticeHolds.lean#L304-L364
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TruncatedLatticeHolds.lean#L304-L364

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

theorem Formalism.LFunctionChainParameters.LLcv.ht_lidx (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {E M : Submodule (𝓞 K) V} (hE : E.FG) (hM : M.FG)
    (h : Submodule.span K (E : Set V) = Submodule.span K (M : Set V)) :
    (Function.support fun p : {p : Ideal (𝓞 K) // p.IsMaximal} =>
        (haveI := p.2.isPrime; lidx p.1 E M)).Finite ∧
      Real.log (ht b X M) = Real.log (ht b X E) +
        ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal}, Real.log (Ideal.absNorm p.1 : ℝ) *
          (haveI := p.2.isPrime; (lidx p.1 E M : ℝ)) := by sorry
