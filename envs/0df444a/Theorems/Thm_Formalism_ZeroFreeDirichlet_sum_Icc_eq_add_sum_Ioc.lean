-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_sum_Icc_eq_add_sum_Ioc
-- name    : Formalism.ZeroFreeDirichlet.sum_Icc_eq_add_sum_Ioc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:44:23.830843+00:00
-- url     : https://prove2.me/theorems/a180421d-ea18-40cc-8a1b-9ba6d5d9436d
-- title:
--   Zero Free Dirichlet: sum Icc eq add sum Ioc
-- statement:
--   The Zero Free Dirichlet construction uses the sum Icc eq add sum Ioc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SumVonMangoldtNotCoprimeLe.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SumVonMangoldtNotCoprimeLe.lean#L13-L17

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

theorem Formalism.ZeroFreeDirichlet.sum_Icc_eq_add_sum_Ioc (g : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Icc 1 b, g n = ∑ n ∈ Icc 1 a, g n + ∑ n ∈ Ioc a b, g n := by sorry
