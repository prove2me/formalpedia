-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_offE_apply
-- name    : Formalism.MainNotions.PlaneGram.offE_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:05:59.334088+00:00
-- url     : https://prove2.me/theorems/8250fed8-30d4-4519-a94c-4c23783b9c8f
-- title:
--   Plane Gram: off E apply
-- statement:
--   The Plane Gram construction uses the off E apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L103-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L103-L107

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

theorem Formalism.MainNotions.PlaneGram.offE_apply (i : L) (α : L × Fin r →₀ ℕ) (j : L) (a : Fin r) :
    offE i α (j, a) = if j = i then 0 else α (j, a) := by sorry
