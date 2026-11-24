-- Prove2me | Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_QuadraticBasis_qb_unit_of_not_dvd
-- name    : Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.qb_unit_of_not_dvd
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:12:22.924735+00:00
-- url     : https://prove2.me/theorems/b7b5d8b7-807b-41db-9a33-9594129a0818
-- title:
--   Quadratic Basis: qb unit of not dvd
-- statement:
--   The Quadratic Basis construction uses the qb unit of not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/QuadraticBasis/QuadBasis.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/QuadraticBasis/QuadBasis.lean#L9-L14

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

theorem Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.qb_unit_of_not_dvd {p : ℕ} (hpW : Irreducible (p : W)) {b : W} (hb : ¬ (p : W) ∣ b) :
    IsUnit b := by sorry
