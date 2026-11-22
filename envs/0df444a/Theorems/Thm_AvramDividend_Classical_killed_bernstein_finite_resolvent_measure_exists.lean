-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_bernstein_finite_resolvent_measure_exists
-- name    : AvramDividend.Classical.killed_bernstein_finite_resolvent_measure_exists
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T15:33:27.993882+00:00
-- url     : https://prove2.me/theorems/5422d653-7371-40c0-a37b-c10636dd0090
-- title:
--   Finite killed Bernstein subordinator resolvent measure via geometric approximation and weak limits
-- statement:
--   For any σ-finite positive-half-line Lévy jump measure κ whose compensated Laplace exponents ∫(1−exp(−st))κ are finite for s>0 and killing k>0, there exists a finite measure U supported on [0,∞), with mass 1/k and Laplace transform 1/(k+∫(1−exp(−st))κ). This is a genuine Bernstein-potential existence theorem, obtained by finite jump truncations, Proved killed-geometric potential 9f7bf7a2, tightness f2895e24 and weak-limit 32aa3f05, without assuming atomlessness. It is the constructive existence component of the original purejump UBV ladder potential.
-- source:
--   Proved 9f7bf7a2, f2895e24, 32aa3f05 and pinned monotone convergence; source purejump killed Bernstein 0cb20c38.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.killed_bernstein_finite_resolvent_measure_exists
    (κ : Measure ℝ) [SFinite κ]
    (hκsupp : κ (Iic (0 : ℝ)) = 0)
    (k : ℝ) (hk : 0 < k)
    (hFin : ∀ s : ℝ, 0 < s →
      (∫⁻ t : ℝ, ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂κ) ≠ ⊤) :
    ∃ U : Measure ℝ,
      U (Iio (0 : ℝ)) = 0 ∧
      U Set.univ = ENNReal.ofReal (k⁻¹) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-(s * y))) ∂U) =
          (ENNReal.ofReal k +
            (∫⁻ t : ℝ,
              ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂κ))⁻¹) := by sorry
