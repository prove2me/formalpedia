-- Prove2me | Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_QuadraticBasis_pbE_mul
-- name    : Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.pbE_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:12:17.127418+00:00
-- url     : https://prove2.me/theorems/e9764cfd-b92f-4476-8c1c-58f921d12041
-- title:
--   Quadratic Basis: pb E mul
-- statement:
--   The Quadratic Basis construction uses the pb E mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/QuadraticBasis/PresIso.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/QuadraticBasis/PresIso.lean#L19-L26

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_StatementO
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_PresIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
variable {W O : Type} [CommRing W] [CommRing O]

theorem Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.pbE_mul (j : W →+* O) (θ w : O) (f0 f1 ϖ : W) (hθ : θ ^ 2 + j f1 * θ + j f0 = 0)
    (hw : w ^ 2 = j ϖ) (t s : W × W × W × W) :
    pbE j θ w t * pbE j θ w s = pbE j θ w (pbM f0 f1 ϖ t s) := by sorry
