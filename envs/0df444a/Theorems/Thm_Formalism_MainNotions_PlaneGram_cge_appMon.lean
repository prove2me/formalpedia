-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_appMon
-- name    : Formalism.MainNotions.PlaneGram.cge_appMon
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:05:49.216336+00:00
-- url     : https://prove2.me/theorems/f4bb6ade-84ff-41d0-b5f8-96b828684a93
-- title:
--   Plane Gram: cge app Mon
-- statement:
--   The Plane Gram construction uses the cge app Mon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L272-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L272-L285

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
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ}
variable {I : Type} [Fintype I]

theorem Formalism.MainNotions.PlaneGram.cge_appMon (v : AddValuation K (WithTop ℚ)) (i : L) (P : ℕ) (cls : I → Fin r → ℕ) (cf : I → K)
    (ρ' δ κ : I → (Fin r →₀ ℕ)) (hcf : ∀ s, 0 ≤ v (cf s)) (α : L × Fin r →₀ ℕ) :
    cge v 0 (appMon i P cls cf ρ' δ κ α) := by sorry
