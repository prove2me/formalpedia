-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_eIn_apply
-- name    : Formalism.MainNotions.PlaneGram.eIn_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:13:16.050916+00:00
-- url     : https://prove2.me/theorems/8487a216-034e-4ce5-b958-0691f8a383b3
-- title:
--   Plane Gram: e In apply
-- statement:
--   The Plane Gram construction uses the e In apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L178-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L178-L181

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
variable {L : Type} {r : ℕ} (out : L → Prop) [DecidablePred out]

theorem Formalism.MainNotions.PlaneGram.eIn_apply (α : L × Fin r →₀ ℕ) (x : L × Fin r) :
    eIn out α x = if out x.1 then 0 else α x := by sorry
