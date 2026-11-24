-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_Slope_trunc
-- name    : Formalism.MainNotions.PlaneGram.Slope.trunc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:03:26.734824+00:00
-- url     : https://prove2.me/theorems/bf98c1a6-c231-4408-a1ff-18c37f929603
-- title:
--   Slope: trunc
-- statement:
--   The Slope construction uses the trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L172-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L172-L193

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

theorem Formalism.MainNotions.PlaneGram.Slope.trunc {f : (σ →₀ ℕ) → K} (sf : Slope v TotallyRealRoots c f) :
    ∃ (ι : Type) (_ : Fintype ι) (lam : ι → K) (n : ι → ℕ) (b : ι → (σ →₀ ℕ) → K),
      (∀ k, 0 ≤ v (lam k)) ∧ (∀ k, n k ≤ 6 * c) ∧ (∀ k, TotallyRealRoots (n k) (b k)) ∧
      (∀ k α, 0 ≤ v (b k α)) ∧ ∀ α, (c : WithTop ℚ) ≤ v (f α - ∑ k, lam k * b k α) := by sorry
