-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_CostOK_prod
-- name    : Formalism.MainNotions.PlaneGram.CostOK.prod
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:03:26.745984+00:00
-- url     : https://prove2.me/theorems/83d480e5-38f2-4208-987e-cd40c442c35d
-- title:
--   Cost OK: prod
-- statement:
--   The Cost OK construction uses the prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L221-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L221-L234

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

theorem Formalism.MainNotions.PlaneGram.CostOK.prod (hC : CostOK TotallyRealRoots) {κ : Type} (s : Finset κ) (n : κ → ℕ) (f : κ → (σ →₀ ℕ) → K)
    (h : ∀ i ∈ s, TotallyRealRoots (n i) (f i)) : TotallyRealRoots (∑ i ∈ s, n i) (fun α => ∏ i ∈ s, f i α) := by sorry
