-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_weightedSum_sub_le
-- name    : Formalism.ZeroFreeDirichlet.norm_weightedSum_sub_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:38:17.767716+00:00
-- url     : https://prove2.me/theorems/3110a3dc-89d1-44cf-910c-831c0e33babf
-- title:
--   Zero Free Dirichlet: norm weighted Sum sub le
-- statement:
--   The Zero Free Dirichlet construction uses the norm weighted Sum sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SumVonMangoldtNotCoprimeLe.lean#L77-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SumVonMangoldtNotCoprimeLe.lean#L77-L81

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

theorem Formalism.ZeroFreeDirichlet.norm_weightedSum_sub_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ Λ n) {y Y : ℝ} (hy : 1 ≤ y) (hyY : y ≤ Y) :
    ‖((y : ℂ) * weightedPartialSumUpTo f Y - (Y : ℂ) * weightedPartialSumUpTo f y) - ((Y - y : ℝ) : ℂ) * partialSumUpTo f y‖
      ≤ (Y - y + 1) * ((Y - y) * Real.log Y) := by sorry
