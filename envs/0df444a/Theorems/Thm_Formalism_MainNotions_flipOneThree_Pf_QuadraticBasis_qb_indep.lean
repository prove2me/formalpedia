-- Prove2me | Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_QuadraticBasis_qb_indep
-- name    : Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.qb_indep
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:12:13.692793+00:00
-- url     : https://prove2.me/theorems/38a399cd-c973-4b08-9ffe-d64308fbebb9
-- title:
--   Quadratic Basis: qb indep
-- statement:
--   The Quadratic Basis construction uses the qb indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/QuadraticBasis/QuadBasis.lean#L116-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/QuadraticBasis/QuadBasis.lean#L116-L122

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_StatementO
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_QuadBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
variable {W O : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]

theorem Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.qb_indep {p : ℕ} (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W)) (hw2 : w ^ 2 = (p : O))
    (hw : Irreducible w) (hθ : ∀ a : W, ¬ w ∣ θ - j a) {a b c d : W}
    (h : j a + j b * θ + j c * w + j d * θ * w = 0) : a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by sorry
