-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_monomial_mem_PolK
-- name    : Formalism.MainNotions.PlaneGram.monomial_mem_PolK
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:07:02.260341+00:00
-- url     : https://prove2.me/theorems/d592b77e-248f-4bd8-bef9-f75c84f82fc7
-- title:
--   Plane Gram: monomial mem Pol K
-- statement:
--   The Plane Gram construction uses the monomial mem Pol K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyBlock.lean#L38-L46

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial

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

theorem Formalism.MainNotions.PlaneGram.monomial_mem_PolK {L : Type} {r : ℕ} (ζ : L × Fin r →₀ ℕ) (c : K) :
    monomial ζ c ∈ PolK K r (fun i => ldeg ζ i) := by sorry
