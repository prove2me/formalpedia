-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_PsiP_support
-- name    : Formalism.MainNotions.PlaneGram.TwistData.PsiP_support
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:04:19.412056+00:00
-- url     : https://prove2.me/theorems/f2024319-118b-40b6-96c5-6ef27984d4ba
-- title:
--   Twist Data: Psi P support
-- statement:
--   The Twist Data construction uses the Psi P support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingTangentIndex.lean#L162-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingTangentIndex.lean#L162-L198

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
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

theorem Formalism.MainNotions.PlaneGram.TwistData.PsiP_support {nc : ℕ} (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r)))
    (hcol : ∀ k, col k ∈ PolK K D.r (fun i => if i ∈ occ k then 1 else 0))
    (hcount : ∀ i, (univ.filter fun k => i ∈ occ k).card = D.dO (D.eA j i))
    (ξ : D.EM) (hξ : ξ ∈ (D.PsiP j col occ).support) :
    D.PostE j ξ ∧ ∀ i, ¬ D.SegL j i → ∀ a, ξ (i, a) = 0 := by sorry
