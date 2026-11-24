-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_vonMangoldtCharIm_zero
-- name    : Formalism.ZeroFreeDirichlet.vonMangoldtCharIm_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:44:45.015413+00:00
-- url     : https://prove2.me/theorems/7b58b714-f1fc-470d-b477-172cd9f2faec
-- title:
--   Zero Free Dirichlet: von Mangoldt Char Im zero
-- statement:
--   The Zero Free Dirichlet construction uses the von Mangoldt Char Im zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L41-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean#L41-L41

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

theorem Formalism.ZeroFreeDirichlet.vonMangoldtCharIm_zero : vonMangoldtCharIm χ 0 = 0 := by sorry
