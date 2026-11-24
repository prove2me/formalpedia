-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_ldeg_mapDomain
-- name    : Formalism.MainNotions.PlaneGram.ldeg_mapDomain
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:07:12.41883+00:00
-- url     : https://prove2.me/theorems/0019e393-7f45-4df7-9da7-b4e3c457e72a
-- title:
--   Plane Gram: ldeg map Domain
-- statement:
--   The Plane Gram construction uses the ldeg map Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/IntegralMonomial.lean#L66-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/IntegralMonomial.lean#L66-L83

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsMonomialOrder
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_IntegralMonomial
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
variable {K : Type} [Field K] {L L' : Type} {r : ℕ}

theorem Formalism.MainNotions.PlaneGram.ldeg_mapDomain [Fintype L] [DecidableEq L] [DecidableEq L'] (f : L → L') (β : L × Fin r →₀ ℕ)
    (i' : L') :
    ldeg (Finsupp.mapDomain (Prod.map f (id : Fin r → Fin r)) β) i' =
      ∑ l, if f l = i' then ldeg β l else 0 := by sorry
