-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_rpow_neg_eq_inv_pow
-- name    : Formalism.ZeroFreeDirichlet.rpow_neg_eq_inv_pow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:44:09.901377+00:00
-- url     : https://prove2.me/theorems/a209c7e4-c961-4ddf-91b2-f278dddb0749
-- title:
--   Zero Free Dirichlet: rpow neg eq inv pow
-- statement:
--   The Zero Free Dirichlet construction uses the rpow neg eq inv pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ExcBoundOf.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ExcBoundOf.lean#L21-L24

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ExcBoundOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.rpow_neg_eq_inv_pow (x ε : ℝ) (hx : 0 < x) (k : ℕ) (hk : 0 < k) :
    x ^ (-ε) = ((x ^ (ε / k)) ^ k)⁻¹ := by sorry
