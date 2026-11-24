-- Prove2me | Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_QuadraticBasis_pbE_add
-- name    : Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.pbE_add
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:12:07.620427+00:00
-- url     : https://prove2.me/theorems/2b46a029-4366-4bfb-88c0-bac5eaf81b42
-- title:
--   Quadratic Basis: pb E add
-- statement:
--   The Quadratic Basis construction uses the pb E add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/QuadraticBasis/PresIso.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/QuadraticBasis/PresIso.lean#L28-L31

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

theorem Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.pbE_add (j : W →+* O) (θ w : O) (t s : W × W × W × W) :
    pbE j θ w t + pbE j θ w s = pbE j θ w (t + s) := by sorry
