-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_binomialUpperTail_le_sqrt_exp
-- name    : FirstPassageLinearTransport.exists_binomialUpperTail_le_sqrt_exp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:21:03.675802+00:00
-- url     : https://prove2.me/theorems/a63ce3cb-effe-5176-8b37-66a1988c107b
-- title:
--   First Passage Linear Transport: exists binomial Upper Tail le sqrt exp
-- statement:
--   Sharp upper-binomial-tail estimate on the central quarter-window.  This is
--   the analytic socket needed by the moving endpoint: the exponential term is
--   exact, while all dependence on the walk length outside the exponent is the
--   single factor `r⁻¹ᐟ²`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L501-L541
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L501-L541

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

theorem FirstPassageLinearTransport.exists_binomialUpperTail_le_sqrt_exp
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ r k : ℕ, 0 < r → 0 < k → k < r →
        (r : ℝ) * (1 / 2 + t₀) ≤ (k : ℝ) →
        (r : ℝ) / 4 ≤ (k : ℝ) →
        (r : ℝ) / 4 ≤ ((r - k : ℕ) : ℝ) →
        (binomialUpperTail r k : ℝ) ≤
          (C / Real.sqrt r) * Real.exp (binomialLogWeight r k) := by sorry
