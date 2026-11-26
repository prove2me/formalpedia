-- Prove2me | Theorems.Thm_CollatzFirstPassage_fixed_polylogarithmic_common_landing_centered_clocks_exact_rate
-- name    : CollatzFirstPassage.fixed_polylogarithmic_common_landing_centered_clocks_exact_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:44:03.059561+00:00
-- url     : https://prove2.me/theorems/ccac6998-8304-5228-9281-aaedd0835b1e
-- title:
--   Collatz First Passage: fixed polylogarithmic common landing centered clocks exact rate
-- statement:
--   The Collatz First Passage construction uses the fixed polylogarithmic common landing centered clocks exact rate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/Solution.lean#L183-L257
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/Solution.lean#L183-L257

import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Definitions.Def_FirstPassageLinearTransport_FixedJointExceptionalOrder
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
import Definitions.Def_FirstPassageLinearTransport_Solution
import Theorems.Thm_FirstPassageLinearTransport_fixed_polylogarithmic_common_landing_centered_clocks_exact_rate

set_option autoImplicit true
open CollatzFirstPassage
open Filter
open scoped BigOperators Real Topology

theorem CollatzFirstPassage.fixed_polylogarithmic_common_landing_centered_clocks_exact_rate
    {A c beta : ℝ}
    (hA : firstPassageCriticalExponent < A)
    (hc : fixedPolylogClockCritical < c)
    (hbeta : 0 < beta) :
    ∃ S : Set ℕ, ∃ C Cexc : ℝ,
      0 < C ∧ 0 < Cexc ∧ NaturalDensityOne S ∧
      (∀ᶠ X : ℕ in atTop,
        (badCount S X : ℝ) ≤
          Cexc * X * (Real.log X) ^
            (-(fixedSharpEndpointMargin A))) ∧
      (∀ᶠ n : ℕ in atTop, n ∈ S →
        ∃ k ell : ℕ,
          (k : ℝ) < c * Real.log n ∧
          |driftGap * (k : ℝ) - (Nat.log 2 n : ℝ)| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          |(2 * driftGap / 3) * (ell : ℝ) - (Nat.log 2 n : ℝ)| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          ell = rawTime n k ∧
          rawOrbit ell n = orbit k n ∧
          (orbit k n : ℝ) < C * (Real.log n) ^ A ∧
          (∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤
              (n : ℝ) * (((Nat.log 2 n : ℝ) + 2) ^
                (fixedSharpEndpointMargin A))) ∧
          (∀ i : ℕ, i ≤ ell →
            (rawOrbit i n : ℝ) ≤
              (n : ℝ) * (((Nat.log 2 n : ℝ) + 2) ^
                (fixedSharpEndpointMargin A)))) := by sorry
