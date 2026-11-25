-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_dg_outside
-- name    : Formalism.MainNotions.PlaneGram.vala_dg_outside
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:51:12.272718+00:00
-- url     : https://prove2.me/theorems/7d83c4bf-b323-4293-ab7e-63e37f0f0021
-- title:
--   Plane Gram: vala dg outside
-- statement:
--   The Plane Gram construction uses the vala dg outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1193-L1205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1193-L1205

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
variable {K : Type} [Field K]
variable {L : Type} [DecidableEq L] {r : ℕ} {sg : L → Bool} {S : Finset L}

theorem Formalism.MainNotions.PlaneGram.vala_dg_outside (out : L → Prop) [DecidablePred out] (hout : ∀ i ∈ S, ¬ out i)
    (g : (L × Fin r →₀ ℕ) → K) (n θ : ℝ)
    (h : ∀ μ, eOut out μ = μ → ∀ G : MvPolynomial (L × Fin r) K, vala sg S θ G →
      vala sg S (θ - n) (dg (fun β => g (μ + β)) G))
    {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) : vala sg S (θ - n) (dg g F) := by sorry
