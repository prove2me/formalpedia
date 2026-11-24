-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_disjoint_eOut_eIn
-- name    : Formalism.MainNotions.PlaneGram.disjoint_eOut_eIn
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:06:43.533779+00:00
-- url     : https://prove2.me/theorems/fde77a2d-2573-46bd-a68d-f53d38a38d39
-- title:
--   Plane Gram: disjoint e Out e In
-- statement:
--   The Plane Gram construction uses the disjoint e Out e In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L331-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L331-L337

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

theorem Formalism.MainNotions.PlaneGram.disjoint_eOut_eIn {L : Type} {r : ℕ} (out : L → Prop) [DecidablePred out]
    (α β : L × Fin r →₀ ℕ) : Disjoint (eOut out α).support (eIn out β).support := by sorry
