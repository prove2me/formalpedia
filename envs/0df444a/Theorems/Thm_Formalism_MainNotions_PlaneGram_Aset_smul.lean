-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_Aset_smul
-- name    : Formalism.MainNotions.PlaneGram.Aset_smul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:04:07.162669+00:00
-- url     : https://prove2.me/theorems/7141df7d-1d65-406c-86fa-fbfaddcee977
-- title:
--   Plane Gram: Aset smul
-- statement:
--   The Plane Gram construction uses the Aset smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L190-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L190-L192

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
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

theorem Formalism.MainNotions.PlaneGram.Aset_smul {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L) (n : ℤ) (a : K)
    {F : MvPolynomial (L × Fin r) K} (h : F ∈ Aset sg S n) : a • F ∈ Aset sg S n := by sorry
