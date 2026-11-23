-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_ldeg_add
-- name    : Formalism.MainNotions.PlaneGram.ldeg_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:25.292729+00:00
-- url     : https://prove2.me/theorems/d6507ff0-ea12-4247-9ea9-fc6b02e81571
-- title:
--   Plane Gram: ldeg add
-- statement:
--   The Plane Gram construction uses the ldeg add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L656-L658
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L656-L658

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
variable {L : Type} {r : ℕ}

theorem Formalism.MainNotions.PlaneGram.ldeg_add (α β : L × Fin r →₀ ℕ) (i : L) : ldeg (α + β) i = ldeg α i + ldeg β i := by sorry
