-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_iteratedDeriv_inv_sub_one_at_two
-- name    : Formalism.ZeroFreeDirichlet.iteratedDeriv_inv_sub_one_at_two
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:42:48.898112+00:00
-- url     : https://prove2.me/theorems/c407aa0c-279c-4ed7-837a-54c192c59f3e
-- title:
--   Zero Free Dirichlet: iterated Deriv inv sub one at two
-- statement:
--   The Zero Free Dirichlet construction uses the iterated Deriv inv sub one at two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/IteratedDerivInvSubOneAtTwo.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/IteratedDerivInvSubOneAtTwo.lean#L10-L14

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_IteratedDerivInvSubOneAtTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped ComplexOrder Nat
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.iteratedDeriv_inv_sub_one_at_two (m : ℕ) :
    iteratedDeriv m (fun s : ℂ => (s - 1)⁻¹) 2 = (-1) ^ m * (m ! : ℂ) := by sorry
