-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_CostOK_sum
-- name    : Formalism.MainNotions.PlaneGram.CostOK.sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:05.624083+00:00
-- url     : https://prove2.me/theorems/adbdf37f-9a59-433b-b483-c4a0d4a08943
-- title:
--   Cost OK: sum
-- statement:
--   The Cost OK construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L206-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L206-L219

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) {σ : Type}
variable {v}
open Formalism.MainNotions.PlaneGram.CostOK
variable {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop}

theorem Formalism.MainNotions.PlaneGram.CostOK.sum (hC : CostOK TotallyRealRoots) {κ : Type} (s : Finset κ) (n : ℕ) (f : κ → (σ →₀ ℕ) → K)
    (h : ∀ i ∈ s, TotallyRealRoots n (f i)) : TotallyRealRoots n (fun α => ∑ i ∈ s, f i α) := by sorry
