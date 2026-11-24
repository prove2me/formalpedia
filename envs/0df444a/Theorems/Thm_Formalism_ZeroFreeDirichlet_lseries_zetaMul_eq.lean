-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_lseries_zetaMul_eq
-- name    : Formalism.ZeroFreeDirichlet.lseries_zetaMul_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:43:21.613437+00:00
-- url     : https://prove2.me/theorems/5244a7bf-c4c9-400f-8691-8d8e231d25ed
-- title:
--   Zero Free Dirichlet: lseries zeta Mul eq
-- statement:
--   The Zero Free Dirichlet construction uses the lseries zeta Mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqCoeff.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqCoeff.lean#L22-L32

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
set_option backward.isDefEq.respectTransparency.types false

theorem Formalism.ZeroFreeDirichlet.lseries_zetaMul_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (DirichletCharacter.zetaMul χ) s = riemannZeta s * DirichletCharacter.LFunction χ s := by sorry
