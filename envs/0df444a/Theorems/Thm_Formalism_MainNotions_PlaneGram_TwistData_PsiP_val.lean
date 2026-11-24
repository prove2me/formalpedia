-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_PsiP_val
-- name    : Formalism.MainNotions.PlaneGram.TwistData.PsiP_val
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:04:01.063511+00:00
-- url     : https://prove2.me/theorems/507972ac-355a-4dfc-a8fe-f7b8734880fe
-- title:
--   Twist Data: Psi P val
-- statement:
--   The Twist Data construction uses the Psi P val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutionXFirstEmbedding.lean#L85-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutionXFirstEmbedding.lean#L85-L130

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
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
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)

theorem Formalism.MainNotions.PlaneGram.TwistData.PsiP_val {nc : ℕ} (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r)))
    (hcol : ∀ k, col k ∈ PolK K D.r (fun i => if i ∈ occ k then 1 else 0))
    (cidx : Fin nc → ℤ) (hts : Fin nc → ℕ) (m : Fin D.r)
    (h14 : ∀ k, 1 ≤ cidx k →
      hts k ≤ ((occ k).filter fun l => l.val < D.stg j m ∧ (D.msg ∘ D.e0 j) l = true).card)
    (h16 : ∀ k, ((colVal (cidx k) (hts k) D.r : ℤ) : WithTop ℤ) ≤
      valS (D.msg ∘ D.e0 j) (initSet (D.nB j + D.r) (D.stg j m)) (col k)) :
    ((∑ k, colVal (cidx k) (hts k) D.r : ℤ) : WithTop ℤ) ≤
      valS D.msg (D.YPset j m) (D.PsiP j col occ) := by sorry
