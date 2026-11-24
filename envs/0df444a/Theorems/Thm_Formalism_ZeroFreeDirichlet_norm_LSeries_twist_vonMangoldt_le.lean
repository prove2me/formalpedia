-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_LSeries_twist_vonMangoldt_le
-- name    : Formalism.ZeroFreeDirichlet.norm_LSeries_twist_vonMangoldt_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:42:48.427356+00:00
-- url     : https://prove2.me/theorems/e55f7b3a-c48f-46a8-a7c5-64edb7ce1c90
-- title:
--   Zero Free Dirichlet: norm LSeries twist von Mangoldt le
-- statement:
--   The Zero Free Dirichlet construction uses the norm LSeries twist von Mangoldt le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LRight.lean#L96-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LRight.lean#L96-L114

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

theorem Formalism.ZeroFreeDirichlet.norm_LSeries_twist_vonMangoldt_le {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    ‖L (↗χ * ↗Λ) s‖ ≤ Formalism.ZF.lamF s.re := by sorry
