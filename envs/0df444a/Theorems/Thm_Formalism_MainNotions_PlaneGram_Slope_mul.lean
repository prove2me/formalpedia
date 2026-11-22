-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_Slope_mul
-- name    : Formalism.MainNotions.PlaneGram.Slope.mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T18:46:14.062063+00:00
-- url     : https://prove2.me/theorems/0fe3054a-736a-47b3-abb7-204d627b3ff6
-- title:
--   Slope: mul
-- statement:
--   The Slope construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L111-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L111-L140

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

theorem Formalism.MainNotions.PlaneGram.Slope.mul (hmul : ∀ m n f g, TotallyRealRoots m f → TotallyRealRoots n g → TotallyRealRoots (m + n) (fun α => f α * g α))
    {f g : (σ →₀ ℕ) → K} (_hf : ∀ α, 0 ≤ v (f α)) (hg : ∀ α, 0 ≤ v (g α))
    (sf : Slope v TotallyRealRoots c f) (sg : Slope v TotallyRealRoots c g) : Slope v TotallyRealRoots c (fun α => f α * g α) := by sorry
