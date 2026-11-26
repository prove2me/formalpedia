-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stirlingSqrtPrefactor_le_of_quarter
-- name    : FirstPassageLinearTransport.stirlingSqrtPrefactor_le_of_quarter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:20:45.248368+00:00
-- url     : https://prove2.me/theorems/e6de3c31-11c0-4ef3-adda-751cd7152556
-- title:
--   First Passage Linear Transport: stirling Sqrt Prefactor le of quarter
-- statement:
--   On the central quarter-window, the square-root factor in Stirling's
--   binomial ratio is uniformly `O(r⁻¹ᐟ²)`.  The deliberately loose constant `4`
--   keeps the statement independent of any endpoint tuning.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L277-L347
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L277-L347

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

theorem FirstPassageLinearTransport.stirlingSqrtPrefactor_le_of_quarter
    {r k : ℕ} (hr : 0 < r) (hk : 0 < k) (hkr : k < r)
    (hkLower : (r : ℝ) / 4 ≤ (k : ℝ))
    (hrkLower : (r : ℝ) / 4 ≤ ((r - k : ℕ) : ℝ)) :
    Real.sqrt (2 * r) /
        (Real.sqrt (2 * k) * Real.sqrt (2 * (r - k))) ≤
      4 / Real.sqrt r := by sorry
