-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_HomD_prod
-- name    : Formalism.MainNotions.PlaneGram.HomD_prod
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:03:25.310347+00:00
-- url     : https://prove2.me/theorems/cab62347-b09e-41e2-9108-38883e6dcea9
-- title:
--   Plane Gram: Hom D prod
-- statement:
--   The Plane Gram construction uses the Hom D prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/IntegralMonomial.lean#L85-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/IntegralMonomial.lean#L85-L109

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

theorem Formalism.MainNotions.PlaneGram.HomD_prod {κ : Type} (s : Finset κ) (d : κ → L → ℕ) (f : κ → MvPolynomial (L × Fin r) K)
    (h : ∀ k ∈ s, HomD (d k) (f k)) : HomD (fun i => ∑ k ∈ s, d k i) (∏ k ∈ s, f k) := by sorry
