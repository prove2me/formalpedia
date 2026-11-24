-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Th_monomial
-- name    : Formalism.MainNotions.PlaneGram.TwistData.Th_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:49.742197+00:00
-- url     : https://prove2.me/theorems/70dd884b-36f6-4a6f-b2ca-a8cf55bbc6f5
-- title:
--   Twist Data: Th monomial
-- statement:
--   The Twist Data construction uses the Th monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MonomialMemPolKSg.lean#L94-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MonomialMemPolKSg.lean#L94-L97

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg
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
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)
variable {ι : Type} [Fintype ι]
variable (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K)

theorem Formalism.MainNotions.PlaneGram.TwistData.Th_monomial (ζ : D.EM) :
    D.Th j cc PP (monomial ζ 1) =
      monomial (eOut (D.outSeg j) ζ) 1 * ∑ b, cc (D.pullE j ζ) b • PP b := by sorry
