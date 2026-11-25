-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ChOK_dg
-- name    : Formalism.MainNotions.PlaneGram.TwistData.ChOK.dg
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:37:13.101321+00:00
-- url     : https://prove2.me/theorems/6ae5ce9c-6e1a-4b63-afa8-822d8fffbe9b
-- title:
--   Ch OK: dg
-- statement:
--   The Ch OK construction uses the dg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SumOnLetterApplyInl.lean#L73-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SumOnLetterApplyInl.lean#L73-L97

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SumOnLetterApplyInl
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
variable [CharZero K] (D : TwistData K) (v : AddValuation K (WithTop ℚ)) (p : ℕ)
variable {D v p}
variable (D p)
variable {D p}

theorem Formalism.MainNotions.PlaneGram.TwistData.ChOK.dg [NeZero D.r] (hV2 : V2 K) {θ : (j : Fin D.J) → Fin (D.nch j) → ℝ} {a : ℝ}
    {G : MvPolynomial (D.OL × Fin D.r) K} (h : D.ChOK v p θ a G) (f : D.EA → K)
    (hf0 : ∀ α, 0 ≤ v (f α)) (T : Finset (D.OL × Fin D.r → ℕ)) (lam : (D.OL × Fin D.r → ℕ) → K)
    (hlam : ∀ m ∈ T, 0 ≤ v (lam m) ∧ ∑ x, m x ≤ 6 * D.c)
    (hf : ∀ α : D.EA, ((D.c : ℕ) : WithTop ℚ) ≤ v (f α - binomComb T lam (fun x => α x))) :
    D.ChOK v p (fun j i => θ j i - 6 * D.c) a (Formalism.MainNotions.PlaneGram.dg f G) := by sorry
