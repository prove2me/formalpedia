-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_chebyshev_smoothing_identity_complex
-- name    : Formalism.ZeroFreeDirichlet.chebyshev_smoothing_identity_complex
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:42:40.409834+00:00
-- url     : https://prove2.me/theorems/0ee9bbd5-b1d0-4765-9ccf-ca7075a0df11
-- title:
--   Zero Free Dirichlet: chebyshev smoothing identity complex
-- statement:
--   The Zero Free Dirichlet construction uses the chebyshev smoothing identity complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PsiChiBoundOf.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PsiChiBoundOf.lean#L12-L18

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SumVonMangoldtNotCoprimeLe
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_AbsZeroTermSecondDifferenceLe
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LeOfSecondDifferenceBound
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PsiChiBoundOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.chebyshev_smoothing_identity_complex (ψ Z SY Sy MY My A : ℂ) (y h : ℝ) :
    ((y * h : ℝ) : ℂ) * (ψ + Z)
      = -(((y : ℂ) * SY - ((y * (1 + h) : ℝ) : ℂ) * Sy) - ((y * (1 + h) - y : ℝ) : ℂ) * ψ)
        + (((y * (1 + h) : ℝ) : ℂ) * My - (y : ℂ) * MY + ((y * h : ℝ) : ℂ) * Z)
        + ((y : ℂ) * (SY - A * ((y * (1 + h) : ℝ) : ℂ) + MY)
            - ((y * (1 + h) : ℝ) : ℂ) * (Sy - A * (y : ℂ) + My)) := by sorry
