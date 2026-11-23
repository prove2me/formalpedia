-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_outSeg_of_not_segL
-- name    : Formalism.MainNotions.PlaneGram.TwistData.outSeg_of_not_segL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:31.789795+00:00
-- url     : https://prove2.me/theorems/9582b6f4-8dd1-4277-9bb1-f24be90bb3d2
-- title:
--   Twist Data: out Seg of not seg L
-- statement:
--   The Twist Data construction uses the out Seg of not seg L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MonomialMemPolKSg.lean#L169-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MonomialMemPolKSg.lean#L169-L179

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

theorem Formalism.MainNotions.PlaneGram.TwistData.outSeg_of_not_segL (i : D.ML) (hi : ¬ D.SegL j i) : D.outSeg j i := by sorry
