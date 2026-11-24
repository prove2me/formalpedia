-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_ddiv_sum
-- name    : Formalism.MainNotions.PlaneGram.ddiv_sum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:06:26.34246+00:00
-- url     : https://prove2.me/theorems/4d5554ec-cee1-44e1-93a8-1aedaefd0b3d
-- title:
--   Plane Gram: ddiv sum
-- statement:
--   The Plane Gram construction uses the ddiv sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DigitPartMonomial.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DigitPartMonomial.lean#L56-L57

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
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

theorem Formalism.MainNotions.PlaneGram.ddiv_sum {σ ι : Type} (M : σ →₀ ℕ) (s : Finset ι) (f : ι → MvPolynomial σ K) :
    ddiv M (∑ i ∈ s, f i) = ∑ i ∈ s, ddiv M (f i) := by sorry
