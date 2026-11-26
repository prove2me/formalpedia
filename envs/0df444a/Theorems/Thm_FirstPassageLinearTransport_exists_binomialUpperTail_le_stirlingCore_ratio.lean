-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_binomialUpperTail_le_stirlingCore_ratio
-- name    : FirstPassageLinearTransport.exists_binomialUpperTail_le_stirlingCore_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:20:55.837984+00:00
-- url     : https://prove2.me/theorems/464531dc-bebb-5633-b0ca-b36a78cc6422
-- title:
--   First Passage Linear Transport: exists binomial Upper Tail le stirling Core ratio
-- statement:
--   Sharp-prefactor upper-tail socket before rewriting the Stirling-core ratio
--   as an entropy exponential.  The constant is uniform in `r` and `k` once the
--   positive displacement margin `t₀` is fixed.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L470-L495
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L470-L495

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.exists_binomialUpperTail_le_stirlingCore_ratio
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ r k : ℕ, 0 < r → 0 < k → k < r →
        (r : ℝ) * (1 / 2 + t₀) ≤ (k : ℝ) →
        (binomialUpperTail r k : ℝ) ≤
          C * stirlingCore r /
            (stirlingCore k * stirlingCore (r - k)) := by sorry
