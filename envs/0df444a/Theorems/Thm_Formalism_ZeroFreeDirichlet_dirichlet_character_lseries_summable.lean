-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_dirichlet_character_lseries_summable
-- name    : Formalism.ZeroFreeDirichlet.dirichlet_character_lseries_summable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:55.24927+00:00
-- url     : https://prove2.me/theorems/0fdbcbce-e3df-4e4b-876e-a8c0c9a1c0ab
-- title:
--   Zero Free Dirichlet: dirichlet character lseries summable
-- statement:
--   The Zero Free Dirichlet construction uses the dirichlet character lseries summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqCoeff.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqCoeff.lean#L10-L13

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ConvolutionNonnegOfDivisors
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_BqCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction
open scoped ComplexOrder LSeries.notation
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.dirichlet_character_lseries_summable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable ⇑(toArithmeticFunction (fun m : ℕ => χ (m : ZMod N))) s := by sorry
