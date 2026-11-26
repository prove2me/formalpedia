-- Prove2me | Theorems.Thm_CollatzFirstPassage_critical_polylogarithmic_descent_with_arbitrary_multipliers
-- name    : CollatzFirstPassage.critical_polylogarithmic_descent_with_arbitrary_multipliers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:37.977717+00:00
-- url     : https://prove2.me/theorems/db1ca050-d0de-4ee2-8a0a-04007ec1e40b
-- title:
--   Collatz First Passage: critical polylogarithmic descent with arbitrary multipliers
-- statement:
--   The Collatz First Passage construction uses the critical polylogarithmic descent with arbitrary multipliers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/Solution.lean#L92-L181
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/Solution.lean#L92-L181

import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Definitions.Def_FirstPassageLinearTransport_FixedJointExceptionalOrder
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
import Definitions.Def_FirstPassageLinearTransport_Solution
import Theorems.Thm_FirstPassageLinearTransport_critical_polylogarithmic_descent_with_arbitrary_multipliers

set_option autoImplicit true
open CollatzFirstPassage
open Filter
open scoped BigOperators Real Topology

theorem CollatzFirstPassage.critical_polylogarithmic_descent_with_arbitrary_multipliers
    {U R : ℕ → ℝ}
    (hUpos : ∀ n, 0 < U n) (hRpos : ∀ n, 0 < R n)
    (hU : Tendsto U atTop atTop) (hR : Tendsto R atTop atTop) :
    ∃ S : Set ℕ, ∃ K : ℝ,
      0 < K ∧ NaturalDensityOne S ∧
      (∀ᶠ n : ℕ in atTop, n ∈ S →
        ∃ k ell : ℕ,
          |driftGap * (k : ℝ) - (Nat.log 2 n : ℝ)| ≤
            K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          |(2 * driftGap / 3) * (ell : ℝ) - (Nat.log 2 n : ℝ)| ≤
            K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          (∀ j : ℕ, j ≤ k →
            |shortcutLogDeviation n j| ≤
              K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          (∀ j : ℕ, j ≤ k →
            |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
              K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          (∀ i : ℕ, i ≤ ell →
            |rawLogDeviation n i| ≤
              K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                Real.log ((Nat.log 2 n : ℝ) + 2))) ∧
          ell = rawTime n k ∧
          rawOrbit ell n = orbit k n ∧
          (orbit k n : ℝ) <
            (Real.log n) ^ firstPassageCriticalExponent * U n ∧
          (∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤ (n : ℝ) * R n) ∧
          (∀ i : ℕ, i ≤ ell →
            (rawOrbit i n : ℝ) ≤ (n : ℝ) * R n) ∧
          (∀ z : ℝ, (orbit k n : ℝ) ≤ z → z ≤ (n : ℝ) →
            |(shortcutFirstPassageTime n z : ℝ) -
                fixedPolylogClockCritical * Real.log ((n : ℝ) / z)| +
              |(rawFirstPassageTime n z : ℝ) -
                (3 / 2) * fixedPolylogClockCritical *
                  Real.log ((n : ℝ) / z)| ≤
                K * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
                  Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
            rawOrbit (rawFirstPassageTime n z) n =
              orbit (shortcutFirstPassageTime n z) n)) := by sorry
