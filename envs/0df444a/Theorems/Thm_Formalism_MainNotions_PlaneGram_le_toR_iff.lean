-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_le_toR_iff
-- name    : Formalism.MainNotions.PlaneGram.le_toR_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:07:23.018456+00:00
-- url     : https://prove2.me/theorems/bc067199-71d6-4d29-b8fa-52bf4dd0a135
-- title:
--   Plane Gram: le to R iff
-- statement:
--   The Plane Gram construction uses the le to R iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L889-L893
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L889-L893

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

theorem Formalism.MainNotions.PlaneGram.le_toR_iff (θ : ℝ) (x : WithTop ℤ) :
    ((θ : ℝ) : WithTop ℝ) ≤ toR x ↔ ((⌈θ⌉ : ℤ) : WithTop ℤ) ≤ x := by sorry
