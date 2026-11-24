-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_negLD_eq_LSeries_mul_vonMangoldt
-- name    : Formalism.ZeroFreeDirichlet.negLD_eq_LSeries_mul_vonMangoldt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:42:15.795981+00:00
-- url     : https://prove2.me/theorems/f878c139-8db5-4da3-a4e6-967f878a6bb2
-- title:
--   Zero Free Dirichlet: neg LD eq LSeries mul von Mangoldt
-- statement:
--   The Zero Free Dirichlet construction uses the neg LD eq LSeries mul von Mangoldt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LRight.lean#L88-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LRight.lean#L88-L94

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaInvBound
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LogDerivRight
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation ArithmeticFunction.Moebius
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.negLD_eq_LSeries_mul_vonMangoldt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    negLD χ s = L (↗χ * ↗Λ) s := by sorry
