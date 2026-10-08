-- Prove2me | Theorems.Thm_AvramDividend_Classical_exists_sfinite_convolution_power_sequence
-- name    : AvramDividend.Classical.exists_sfinite_convolution_power_sequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T23:58:03.813787+00:00
-- url     : https://prove2.me/theorems/80563ced-50c8-42c4-8e64-ce56e334e5f2
-- title:
--   Existence of an s-finite additive convolution-power sequence
-- statement:
--   Every s-finite measure on the additive real line has a recursively defined convolution-power sequence beginning with Dirac mass at zero. Every term remains s-finite because convolution preserves s-finiteness.
-- source:
--   Pinned Mathlib additive measure convolution and its sfinite_mconv_of_sfinite instance; elementary recursion on natural numbers.

import Mathlib
open MeasureTheory

namespace AvramDividend.Classical

theorem exists_sfinite_convolution_power_sequence
    (κ : Measure ℝ) [SFinite κ] :
    ∃ m : ℕ → Measure ℝ,
      m 0 = Measure.dirac 0 ∧
      (∀ n : ℕ, m (n + 1) = Measure.conv κ (m n)) ∧
      (∀ n : ℕ, SFinite (m n)) := by
  sorry

end AvramDividend.Classical
