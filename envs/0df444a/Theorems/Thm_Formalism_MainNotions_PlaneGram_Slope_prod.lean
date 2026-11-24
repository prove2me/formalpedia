-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_Slope_prod
-- name    : Formalism.MainNotions.PlaneGram.Slope.prod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:03:05.653795+00:00
-- url     : https://prove2.me/theorems/302c03de-a210-46f9-a161-240d3f617056
-- title:
--   Slope: prod
-- statement:
--   The Slope construction uses the prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L142-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L142-L160

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
open Formalism.MainNotions.PlaneGram.Slope
variable {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop} {c : ℕ}

theorem Formalism.MainNotions.PlaneGram.Slope.prod (h1 : TotallyRealRoots 0 (fun _ => 1))
    (hmul : ∀ m n f g, TotallyRealRoots m f → TotallyRealRoots n g → TotallyRealRoots (m + n) (fun α => f α * g α))
    {κ : Type} (s : Finset κ) (f : κ → (σ →₀ ℕ) → K) (hf : ∀ i ∈ s, ∀ α, 0 ≤ v (f i α))
    (sf : ∀ i ∈ s, Slope v TotallyRealRoots c (f i)) : Slope v TotallyRealRoots c (fun α => ∏ i ∈ s, f i α) := by sorry
