-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_good_Pj
-- name    : Formalism.MainNotions.PlaneGram.good_Pj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:07:34.070056+00:00
-- url     : https://prove2.me/theorems/a9aba224-ec8c-46d9-95da-f3569524d663
-- title:
--   Plane Gram: good Pj
-- statement:
--   The Plane Gram construction uses the good Pj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MlabNotMemYset.lean#L54-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MlabNotMemYset.lean#L54-L62

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MlabNotMemYset
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
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

theorem Formalism.MainNotions.PlaneGram.good_Pj (D : TwistData K)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hP1 : ∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → (∀ i, ldeg ζ' i = ldeg ζ i) ∧
        (∀ t a, ζ' (D.mlab t, a) = ζ (D.mlab t, a)) ∧ (∀ t a, ζ' (D.mtp t, a) = ζ (D.mtp t, a)))
    {Y : MvPolynomial (D.ML × Fin D.r) K} (hY : D.Good p Y) : D.Good p (Pj Y) := by sorry
