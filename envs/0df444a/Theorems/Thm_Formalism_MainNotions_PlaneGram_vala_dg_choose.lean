-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_dg_choose
-- name    : Formalism.MainNotions.PlaneGram.vala_dg_choose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:22.455701+00:00
-- url     : https://prove2.me/theorems/d2b906e4-5ca8-4d65-b31f-e6a234edcb9a
-- title:
--   Plane Gram: vala dg choose
-- statement:
--   The Plane Gram construction uses the vala dg choose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1113-L1131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1113-L1131

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
variable {K : Type} [Field K] [CharZero K] {L : Type} [Fintype L] [DecidableEq L] {r : ℕ} [NeZero r]
  {sg : L → Bool} {S : Finset L}

theorem Formalism.MainNotions.PlaneGram.vala_dg_choose (hV2 : V2 K) {θ : ℝ} (x : L × Fin r) (k : ℕ)
    {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) :
    vala sg S (θ - k) (dg (fun α => ((α x).choose k : K)) F) := by sorry
