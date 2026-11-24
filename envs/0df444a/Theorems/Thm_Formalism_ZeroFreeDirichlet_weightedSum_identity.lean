-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_weightedSum_identity
-- name    : Formalism.ZeroFreeDirichlet.weightedSum_identity
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:43:57.506792+00:00
-- url     : https://prove2.me/theorems/798c0c21-eeac-4387-8a70-7b8bfbad20e7
-- title:
--   Zero Free Dirichlet: weighted Sum identity
-- statement:
--   The Zero Free Dirichlet construction uses the weighted Sum identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SumVonMangoldtNotCoprimeLe.lean#L19-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SumVonMangoldtNotCoprimeLe.lean#L19-L29

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

theorem Formalism.ZeroFreeDirichlet.weightedSum_identity (f : ℕ → ℂ) {y Y : ℝ} (hyY : y ≤ Y) :
    (y : ℂ) * weightedPartialSumUpTo f Y - (Y : ℂ) * weightedPartialSumUpTo f y
      = ((Y - y : ℝ) : ℂ) * partialSumUpTo f y
        + ∑ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, f n * ((y * (Y / n - 1) : ℝ) : ℂ) := by sorry
