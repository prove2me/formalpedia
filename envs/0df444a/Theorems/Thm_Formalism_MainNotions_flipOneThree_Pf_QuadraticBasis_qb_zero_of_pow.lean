-- Prove2me | Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_QuadraticBasis_qb_zero_of_pow
-- name    : Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.qb_zero_of_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:12:16.338047+00:00
-- url     : https://prove2.me/theorems/66109e17-d5a3-47be-89c2-51a0e6609f00
-- title:
--   Quadratic Basis: qb zero of pow
-- statement:
--   The Quadratic Basis construction uses the qb zero of pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/QuadraticBasis/QuadBasis.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/QuadraticBasis/QuadBasis.lean#L111-L114

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

theorem Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.qb_zero_of_pow {p : ℕ} (hpW : Irreducible (p : W)) {a : W} (h : ∀ m, (p : W) ^ m ∣ a) : a = 0 := by sorry
