-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_le_valS_iff
-- name    : Formalism.MainNotions.PlaneGram.le_valS_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T19:16:58.248654+00:00
-- url     : https://prove2.me/theorems/81fb9d20-b12f-4533-b1e0-dc88939f6f4e
-- title:
--   Plane Gram: le val S iff
-- statement:
--   The Plane Gram construction uses the le val S iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L115-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L115-L118

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

theorem Formalism.MainNotions.PlaneGram.le_valS_iff (n : WithTop ℤ) (F : MvPolynomial (L × Fin r) K) :
    n ≤ valS sg S F ↔ ∀ β, n ≤ lord ((subV sg S F).coeff β) := by sorry
