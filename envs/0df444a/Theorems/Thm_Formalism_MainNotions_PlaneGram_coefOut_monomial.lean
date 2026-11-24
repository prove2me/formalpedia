-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_coefOut_monomial
-- name    : Formalism.MainNotions.PlaneGram.coefOut_monomial
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:06:52.622219+00:00
-- url     : https://prove2.me/theorems/a16eadff-3591-4eea-a6ea-1158b2d5edf7
-- title:
--   Plane Gram: coef Out monomial
-- statement:
--   The Plane Gram construction uses the coef Out monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L402-L405
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L402-L405

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
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ}
  (out : L → Prop) [DecidablePred out]

theorem Formalism.MainNotions.PlaneGram.coefOut_monomial (μ α : L × Fin r →₀ ℕ) (c : K) :
    coefOut out μ (monomial α c) = if eOut out α = μ then monomial (eIn out α) c else 0 := by sorry
