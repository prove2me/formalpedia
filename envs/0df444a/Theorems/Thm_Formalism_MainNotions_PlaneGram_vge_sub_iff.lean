-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_sub_iff
-- name    : Formalism.MainNotions.PlaneGram.vge_sub_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:10:29.860448+00:00
-- url     : https://prove2.me/theorems/77971405-4845-4580-995d-776835aee8cb
-- title:
--   Plane Gram: vge sub iff
-- statement:
--   The Plane Gram construction uses the vge sub iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L190-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L190-L196

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
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
variable (v : AddValuation K (WithTop ℚ)) {σ : Type}

theorem Formalism.MainNotions.PlaneGram.vge_sub_iff (a w : ℝ) (x : K) :
    vge v (a - w) x ↔ ((a : ℝ) : WithTop ℝ) ≤ vR v x + ((w : ℝ) : WithTop ℝ) := by sorry
