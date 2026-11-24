-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_one_apply_natCast
-- name    : Formalism.ZeroFreeDirichlet.one_apply_natCast
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:42:58.636278+00:00
-- url     : https://prove2.me/theorems/5f206292-8cc1-46ca-9f73-2acbbd245a5d
-- title:
--   Zero Free Dirichlet: one apply nat Cast
-- statement:
--   The Zero Free Dirichlet construction uses the one apply nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SumVonMangoldtNotCoprimeLe.lean#L111-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SumVonMangoldtNotCoprimeLe.lean#L111-L115

import Mathlib
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SumVonMangoldtNotCoprimeLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.one_apply_natCast {q : ℕ} (n : ℕ) :
    (1 : DirichletCharacter ℂ q) (n : ZMod q) = if n.Coprime q then 1 else 0 := by sorry
