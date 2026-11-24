-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_one_sub_prime_cpow_neg_ne_zero
-- name    : Formalism.ZeroFreeDirichlet.one_sub_prime_cpow_neg_ne_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:43:14.381022+00:00
-- url     : https://prove2.me/theorems/aacb2c24-a3aa-46fa-8a46-513325a4baef
-- title:
--   Zero Free Dirichlet: one sub prime cpow neg ne zero
-- statement:
--   The Zero Free Dirichlet construction uses the one sub prime cpow neg ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/TrivReal.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/TrivReal.lean#L9-L17

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_TrivReal
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

theorem Formalism.ZeroFreeDirichlet.one_sub_prime_cpow_neg_ne_zero (p : ℕ) (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by sorry
