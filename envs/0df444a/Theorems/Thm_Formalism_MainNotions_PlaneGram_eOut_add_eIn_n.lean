-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_add_eIn_n
-- name    : Formalism.MainNotions.PlaneGram.eOut_add_eIn_n
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:06:19.023295+00:00
-- url     : https://prove2.me/theorems/b4f3679d-18bb-4f28-b499-edf049df5d3d
-- title:
--   Plane Gram: e Out add e In n
-- statement:
--   The Plane Gram construction uses the e Out add e In n property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L326-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L326-L329

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
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
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))

theorem Formalism.MainNotions.PlaneGram.eOut_add_eIn_n {L : Type} {r : ℕ} (out : L → Prop) [DecidablePred out] (α : L × Fin r →₀ ℕ) :
    eOut out α + eIn out α = α := by sorry
