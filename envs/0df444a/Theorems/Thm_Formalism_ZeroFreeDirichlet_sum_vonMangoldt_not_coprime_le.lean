-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_sum_vonMangoldt_not_coprime_le
-- name    : Formalism.ZeroFreeDirichlet.sum_vonMangoldt_not_coprime_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:44:28.247874+00:00
-- url     : https://prove2.me/theorems/d3e48634-c9f4-448c-b98a-74a218d52332
-- title:
--   Zero Free Dirichlet: sum von Mangoldt not coprime le
-- statement:
--   The Zero Free Dirichlet construction uses the sum von Mangoldt not coprime le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SumVonMangoldtNotCoprimeLe.lean#L83-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SumVonMangoldtNotCoprimeLe.lean#L83-L109

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

theorem Formalism.ZeroFreeDirichlet.sum_vonMangoldt_not_coprime_le (q : ℕ) (hq : q ≠ 0) (N : ℕ) :
    ∑ n ∈ Icc 1 N, Λ n * (if n.Coprime q then 0 else 1) ≤ (Nat.log 2 N : ℝ) * Real.log q := by sorry
