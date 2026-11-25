-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_prod
-- name    : Formalism.MainNotions.PlaneGram.vala_prod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:51:10.599561+00:00
-- url     : https://prove2.me/theorems/370ca184-847b-4feb-873c-2f27b7d58cf7
-- title:
--   Plane Gram: vala prod
-- statement:
--   The Plane Gram construction uses the vala prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L995-L1003
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L995-L1003

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L)
variable {sg S}

theorem Formalism.MainNotions.PlaneGram.vala_prod {ι : Type} (s : Finset ι) (θ : ι → ℝ) (f : ι → MvPolynomial (L × Fin r) K)
    (h : ∀ i ∈ s, vala sg S (θ i) (f i)) : vala sg S (∑ i ∈ s, θ i) (∏ i ∈ s, f i) := by sorry
