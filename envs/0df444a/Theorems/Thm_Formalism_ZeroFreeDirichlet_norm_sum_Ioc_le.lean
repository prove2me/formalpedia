-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_sum_Ioc_le
-- name    : Formalism.ZeroFreeDirichlet.norm_sum_Ioc_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:42:56.793849+00:00
-- url     : https://prove2.me/theorems/effc3c51-f710-4167-bd0a-6a8b1211c35b
-- title:
--   Zero Free Dirichlet: norm sum Ioc le
-- statement:
--   The Zero Free Dirichlet construction uses the norm sum Ioc le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SumVonMangoldtNotCoprimeLe.lean#L31-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SumVonMangoldtNotCoprimeLe.lean#L31-L75

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

theorem Formalism.ZeroFreeDirichlet.norm_sum_Ioc_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ Λ n) {y Y : ℝ} (hy : 1 ≤ y) (hyY : y ≤ Y) :
    ‖∑ n ∈ Ioc ⌊y⌋₊ ⌊Y⌋₊, f n * ((y * (Y / n - 1) : ℝ) : ℂ)‖
      ≤ (Y - y + 1) * ((Y - y) * Real.log Y) := by sorry
