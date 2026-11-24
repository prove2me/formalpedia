-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_dg_labels
-- name    : Formalism.MainNotions.PlaneGram.vala_dg_labels
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:08:03.962886+00:00
-- url     : https://prove2.me/theorems/f12324a8-50ab-4074-9eb9-cea4e6abea7d
-- title:
--   Plane Gram: vala dg labels
-- statement:
--   The Plane Gram construction uses the vala dg labels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/PrimedEmbeddingInjective.lean#L99-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/PrimedEmbeddingInjective.lean#L99-L132

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CollapseExponent
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_PrimedEmbeddingInjective
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
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}

theorem Formalism.MainNotions.PlaneGram.vala_dg_labels (D : TwistData K) (gg : (D.Tau → Fin D.r → ℕ) → D.EM → K) (n : ℕ)
    (hgg : ∀ ρ, CostM D n (gg ρ)) (S : Finset D.ML) (hS : ∀ t, D.mlab t ∉ S) (θ : ℝ)
    (Z : MvPolynomial (D.ML × Fin D.r) K) (hZ : vala D.msg S θ Z) :
    vala D.msg S (θ - n) (dg (fun ζ => gg (D.labF ζ) ζ) Z) := by sorry
