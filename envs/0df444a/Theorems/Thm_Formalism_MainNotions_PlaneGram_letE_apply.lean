-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_letE_apply
-- name    : Formalism.MainNotions.PlaneGram.letE_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:16:52.848797+00:00
-- url     : https://prove2.me/theorems/e50a9791-addf-403f-853c-b9d97e852811
-- title:
--   Plane Gram: let E apply
-- statement:
--   The Plane Gram construction uses the let E apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L99-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L99-L99

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
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
variable {L : Type} [DecidableEq L] {r : ℕ}

theorem Formalism.MainNotions.PlaneGram.letE_apply (α : L × Fin r →₀ ℕ) (i : L) (a : Fin r) : letE α i a = α (i, a) := by sorry

attribute [defeq] Formalism.MainNotions.PlaneGram.letE_apply
