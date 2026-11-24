-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_appMon_eq
-- name    : Formalism.MainNotions.PlaneGram.appMon_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:05:43.573181+00:00
-- url     : https://prove2.me/theorems/bbee001b-eea3-4eee-a229-58803a19d13e
-- title:
--   Plane Gram: app Mon eq
-- statement:
--   The Plane Gram construction uses the app Mon eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L261-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L261-L270

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
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
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ}
variable {I : Type} [Fintype I]

theorem Formalism.MainNotions.PlaneGram.appMon_eq (i : L) (P : ℕ) (cls : I → Fin r → ℕ) (cf : I → K) (ρ' δ κ : I → (Fin r →₀ ℕ))
    (α : L × Fin r →₀ ℕ) :
    appMon i P cls cf ρ' δ κ α = putL i α (∑ s, if cls s = (fun a => letE α i a % P) then
      monomial (ρ' s + P • (δ s + (divE P (letE α i) - κ s))) (cf s * bin (κ s) (divE P (letE α i)))
      else 0) := by sorry
