-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_choose_affine
-- name    : Formalism.MainNotions.PlaneGram.choose_affine
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:06:50.718602+00:00
-- url     : https://prove2.me/theorems/5c48a015-3a17-4003-98a9-fbed3c789673
-- title:
--   Plane Gram: choose affine
-- statement:
--   The Plane Gram construction uses the choose affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L256-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L256-L288

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

theorem Formalism.MainNotions.PlaneGram.choose_affine (ρ P m : ℕ) : ∃ z : ℕ → ℕ, ∀ β : ℕ,
    (ρ + P * β).choose m = ∑ i ∈ range (m + 1), z i * β.choose i := by sorry
