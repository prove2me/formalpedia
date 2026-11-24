-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Th_away
-- name    : Formalism.MainNotions.PlaneGram.TwistData.Th_away
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:04:22.054176+00:00
-- url     : https://prove2.me/theorems/aecfd80c-ddd2-4e5e-a586-c1120965c91f
-- title:
--   Twist Data: Th away
-- statement:
--   The Twist Data construction uses the Th away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MonomialMemPolKSg.lean#L223-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MonomialMemPolKSg.lean#L223-L251

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg
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
variable {ι : Type} [Fintype ι]
variable (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K)

theorem Formalism.MainNotions.PlaneGram.TwistData.Th_away (hPP : ∀ b, ∀ ξ ∈ (PP b).support, ∀ i, ¬ D.SegL j i → ∀ a, ξ (i, a) = 0)
    (S : Finset D.ML) (hS : ∀ i ∈ S, ¬ D.SegL j i) (Z : MvPolynomial (D.ML × Fin D.r) K) :
    valS D.msg S Z ≤ valS D.msg S (D.Th j cc PP Z) := by sorry
