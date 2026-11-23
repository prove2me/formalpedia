-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_dirichlet_character_lseries_eq
-- name    : Formalism.ZeroFreeDirichlet.dirichlet_character_lseries_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:58.438567+00:00
-- url     : https://prove2.me/theorems/cb8eec80-feea-47b6-83cf-da4f37e41575
-- title:
--   Zero Free Dirichlet: dirichlet character lseries eq
-- statement:
--   The Zero Free Dirichlet construction uses the dirichlet character lseries eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqCoeff.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqCoeff.lean#L15-L19

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

theorem Formalism.ZeroFreeDirichlet.dirichlet_character_lseries_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries ⇑(toArithmeticFunction (fun m : ℕ => χ (m : ZMod N))) s = DirichletCharacter.LFunction χ s := by sorry
