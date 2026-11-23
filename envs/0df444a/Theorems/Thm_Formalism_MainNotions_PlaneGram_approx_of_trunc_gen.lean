-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_approx_of_trunc_gen
-- name    : Formalism.MainNotions.PlaneGram.approx_of_trunc_gen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:48.928604+00:00
-- url     : https://prove2.me/theorems/8822cb3d-1b56-4318-a2f2-17713254c7e7
-- title:
--   Plane Gram: approx of trunc gen
-- statement:
--   The Plane Gram construction uses the approx of trunc gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L334-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L334-L346

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

theorem Formalism.MainNotions.PlaneGram.approx_of_trunc_gen (hC : CostOK TotallyRealRoots) {κ : Type} [Fintype κ] (u : κ → (σ →₀ ℕ) → ℕ)
    (hu : ∀ a k, TotallyRealRoots k (fun α => ((u a α).choose k : K)))
    (T : Finset (κ → ℕ)) (lam : (κ → ℕ) → K) {c n : ℕ}
    (hlam : ∀ m ∈ T, 0 ≤ v (lam m) ∧ ∑ a, m a ≤ n) (f : (σ →₀ ℕ) → K)
    (hf : ∀ α, (c : WithTop ℚ) ≤ v (f α - binomComb T lam (fun a => u a α))) :
    ∃ g : (σ →₀ ℕ) → K, (∀ α, 0 ≤ v (g α)) ∧ (∀ α, (c : WithTop ℚ) ≤ v (f α - g α)) ∧ TotallyRealRoots n g := by sorry
