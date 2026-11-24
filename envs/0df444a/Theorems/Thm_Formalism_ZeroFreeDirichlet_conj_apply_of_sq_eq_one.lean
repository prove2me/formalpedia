-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_conj_apply_of_sq_eq_one
-- name    : Formalism.ZeroFreeDirichlet.conj_apply_of_sq_eq_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:43:01.504516+00:00
-- url     : https://prove2.me/theorems/91289b4a-de9b-4dc5-9781-36c61c68cf3c
-- title:
--   Zero Free Dirichlet: conj apply of sq eq one
-- statement:
--   The Zero Free Dirichlet construction uses the conj apply of sq eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/TrivReal.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/TrivReal.lean#L31-L39

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

theorem Formalism.ZeroFreeDirichlet.conj_apply_of_sq_eq_one {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (a : ZMod q) :
    starRingEnd ℂ (χ a) = χ a := by sorry
