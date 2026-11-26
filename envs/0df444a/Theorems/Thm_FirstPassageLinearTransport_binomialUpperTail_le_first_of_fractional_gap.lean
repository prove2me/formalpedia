-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_binomialUpperTail_le_first_of_fractional_gap
-- name    : FirstPassageLinearTransport.binomialUpperTail_le_first_of_fractional_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:20:27.703922+00:00
-- url     : https://prove2.me/theorems/4f9233ea-f100-4388-acbb-ef5234362752
-- title:
--   First Passage Linear Transport: binomial Upper Tail le first of fractional gap
-- statement:
--   On a fixed positive displacement window, the entire binomial upper tail
--   is bounded by a uniform multiple of its first coefficient.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L177-L217
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L177-L217

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

theorem FirstPassageLinearTransport.binomialUpperTail_le_first_of_fractional_gap
    {t₀ : ℝ} (ht₀ : 0 < t₀) {r k : ℕ}
    (hr : 0 < r) (hkr : k ≤ r)
    (hgap : (r : ℝ) * (1 / 2 + t₀) ≤ (k : ℝ)) :
    (binomialUpperTail r k : ℝ) ≤
      (1 / (2 * t₀)) * (r.choose k : ℝ) := by sorry
