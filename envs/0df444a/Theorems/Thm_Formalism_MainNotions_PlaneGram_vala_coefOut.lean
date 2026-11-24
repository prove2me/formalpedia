-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_coefOut
-- name    : Formalism.MainNotions.PlaneGram.vala_coefOut
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:46:45.943808+00:00
-- url     : https://prove2.me/theorems/0bb6c7e9-9283-489a-b504-25349aab0089
-- title:
--   Plane Gram: vala coef Out
-- statement:
--   The Plane Gram construction uses the vala coef Out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1005-L1007
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1005-L1007

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

theorem Formalism.MainNotions.PlaneGram.vala_coefOut {θ : ℝ} (out : L → Prop) [DecidablePred out] (hout : ∀ i ∈ S, ¬ out i)
    (μ : L × Fin r →₀ ℕ) {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) :
    vala sg S θ (coefOut out μ F) := by sorry
