-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_fact_EM
-- name    : Formalism.MainNotions.PlaneGram.TwistData.fact_EM
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:05:17.104853+00:00
-- url     : https://prove2.me/theorems/c33ed5f5-1587-4dde-bff3-a921f6e81064
-- title:
--   Twist Data: fact EM
-- statement:
--   The Twist Data construction uses the fact EM property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/GlobalTheory.lean#L136-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/GlobalTheory.lean#L136-L142

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
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
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)
variable [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}
omit [CharZero K]

theorem Formalism.MainNotions.PlaneGram.TwistData.fact_EM (ζ : D.EM) : fact ζ = (∏ b, ∏ a, (ζ (D.mb b, a)).factorial) *
    ((∏ t, ∏ a, (ζ (D.mlab t, a)).factorial) * ((∏ t, ∏ a, (ζ (D.mw t, a)).factorial) *
      ∏ t, ∏ a, (ζ (D.mtp t, a)).factorial)) := by sorry
