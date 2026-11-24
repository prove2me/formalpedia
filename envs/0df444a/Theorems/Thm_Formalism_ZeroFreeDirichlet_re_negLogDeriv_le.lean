-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_re_negLogDeriv_le
-- name    : Formalism.ZeroFreeDirichlet.re_negLogDeriv_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:44:19.882309+00:00
-- url     : https://prove2.me/theorems/e5f108bc-772b-490f-aac2-ef27d161d7ca
-- title:
--   Zero Free Dirichlet: re neg Log Deriv le
-- statement:
--   The Zero Free Dirichlet construction uses the re neg Log Deriv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/EulerFactorLogDerivBound.lean#L49-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/EulerFactorLogDerivBound.lean#L49-L105

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_EulerFactorLogDerivBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.re_negLogDeriv_le (q : ℕ) [NeZero q] (s : ℂ) (hs : 1 < s.re) :
    (negLD (1 : DirichletCharacter ℂ q) s).re ≤
      (-(deriv riemannZeta s / riemannZeta s)).re + Real.log q := by sorry
