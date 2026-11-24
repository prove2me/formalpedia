-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Th_supp
-- name    : Formalism.MainNotions.PlaneGram.TwistData.Th_supp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:04:16.836801+00:00
-- url     : https://prove2.me/theorems/90207720-dc0b-40ec-af73-1e3a44e1ac95
-- title:
--   Twist Data: Th supp
-- statement:
--   The Twist Data construction uses the Th supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MonomialMemPolKSg.lean#L156-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MonomialMemPolKSg.lean#L156-L167

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

theorem Formalism.MainNotions.PlaneGram.TwistData.Th_supp (ζ ζ' : D.EM) (h : ζ' ∈ (D.Th j cc PP (monomial ζ 1)).support) :
    ∃ b, ∃ ξ ∈ (PP b).support, ζ' = eOut (D.outSeg j) ζ + ξ := by sorry
