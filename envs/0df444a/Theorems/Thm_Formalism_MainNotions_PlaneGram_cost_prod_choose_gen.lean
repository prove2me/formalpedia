-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_cost_prod_choose_gen
-- name    : Formalism.MainNotions.PlaneGram.cost_prod_choose_gen
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:06:28.186131+00:00
-- url     : https://prove2.me/theorems/14c67104-fb50-4a50-98d0-37e63d5d5d06
-- title:
--   Plane Gram: cost prod choose gen
-- statement:
--   The Plane Gram construction uses the cost prod choose gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L311-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L311-L317

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
variable {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop}

theorem Formalism.MainNotions.PlaneGram.cost_prod_choose_gen (h1 : TotallyRealRoots 0 (fun _ => 1))
    (hmul : ∀ m n f g, TotallyRealRoots m f → TotallyRealRoots n g → TotallyRealRoots (m + n) (fun α => f α * g α))
    {κ : Type} [Fintype κ] (u : κ → (σ →₀ ℕ) → ℕ)
    (hu : ∀ a k, TotallyRealRoots k (fun α => ((u a α).choose k : K))) (m : κ → ℕ) :
    TotallyRealRoots (∑ a, m a) (fun α => ∏ a, ((u a α).choose (m a) : K)) := by sorry
