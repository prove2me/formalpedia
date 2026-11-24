-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_digitPart_appL
-- name    : Formalism.MainNotions.PlaneGram.TwistData.digitPart_appL
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:03:59.178898+00:00
-- url     : https://prove2.me/theorems/18015d85-de53-4367-835f-ecaa255b5ad3
-- title:
--   Twist Data: digit Part app L
-- statement:
--   The Twist Data construction uses the digit Part app L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L509-L524
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L509-L524

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
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K) (p : ℕ)
variable (t : D.Tau)

theorem Formalism.MainNotions.PlaneGram.TwistData.digitPart_appL {I : Type} [Fintype I] (hP : 0 < D.P p t) (ρ'' : D.Tau → Fin D.r → ℕ)
    (cls : I → Fin D.r → ℕ) (cf : I → K) (ρ' δ κ : I → (Fin D.r →₀ ℕ))
    (G : MvPolynomial (D.OL × Fin D.r) K) :
    D.digitPart p ρ'' (appL (Sum.inr t) (D.P p t) cls cf ρ' δ κ G) =
      ∑ s, if (fun a => ρ' s a % D.P p t) = ρ'' t then
        D.opS t (divE (D.P p t) (ρ' s) + δ s) (κ s) (cf s)
          (D.digitPart p (Function.update ρ'' t (cls s)) G) else 0 := by sorry
