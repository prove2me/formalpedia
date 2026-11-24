-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_term_twist_moebius_le
-- name    : Formalism.ZeroFreeDirichlet.norm_term_twist_moebius_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:43:10.595783+00:00
-- url     : https://prove2.me/theorems/6d0b4a77-ac02-4ace-9ff6-4ce9c1b4aa7d
-- title:
--   Zero Free Dirichlet: norm term twist moebius le
-- statement:
--   The Zero Free Dirichlet construction uses the norm term twist moebius le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LRight.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LRight.lean#L12-L20

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

theorem Formalism.ZeroFreeDirichlet.norm_term_twist_moebius_le {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (n : ℕ) :
    ‖term (↗χ * ↗μ) s n‖ ≤ ‖term (1 : ℕ → ℂ) s n‖ := by sorry
