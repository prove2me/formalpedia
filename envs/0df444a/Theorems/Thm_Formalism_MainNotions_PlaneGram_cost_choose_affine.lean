-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_cost_choose_affine
-- name    : Formalism.MainNotions.PlaneGram.cost_choose_affine
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:53.928428+00:00
-- url     : https://prove2.me/theorems/e1ca90e0-fd37-420e-b02d-3c63fdf6aedb
-- title:
--   Plane Gram: cost choose affine
-- statement:
--   The Plane Gram construction uses the cost choose affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L319-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L319-L332

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

theorem Formalism.MainNotions.PlaneGram.cost_choose_affine (hC : CostOK TotallyRealRoots) (u : (σ →₀ ℕ) → ℕ)
    (hu : ∀ k, TotallyRealRoots k (fun α => ((u α).choose k : K))) (ρ P m : ℕ) :
    TotallyRealRoots m (fun α => ((ρ + P * u α).choose m : K)) := by sorry
