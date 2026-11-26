-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_normalized_binomialUpperTail_le_binaryBarrierRate
-- name    : FirstPassageLinearTransport.exists_normalized_binomialUpperTail_le_binaryBarrierRate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:30:33.235939+00:00
-- url     : https://prove2.me/theorems/51dc2b3c-ca59-4fa1-a89d-6580d7f102e1
-- title:
--   First Passage Linear Transport: exists normalized binomial Upper Tail le binary Barrier Rate
-- statement:
--   Probability-scale version of the sharp binomial-tail socket.  Dividing
--   by the Boolean mass `2^r` converts the entropy exponential exactly into the
--   canonical binary barrier rate.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L546-L584
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L546-L584

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

theorem FirstPassageLinearTransport.exists_normalized_binomialUpperTail_le_binaryBarrierRate
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ r k : ℕ, 0 < r → 0 < k → k < r →
        (r : ℝ) * (1 / 2 + t₀) ≤ (k : ℝ) →
        (r : ℝ) / 4 ≤ (k : ℝ) →
        (r : ℝ) / 4 ≤ ((r - k : ℕ) : ℝ) →
        (binomialUpperTail r k : ℝ) / (2 : ℝ) ^ r ≤
          (C / Real.sqrt r) *
            Real.exp (-((r : ℝ) *
              binaryBarrierRate ((k : ℝ) / (r : ℝ) - 1 / 2))) := by sorry
