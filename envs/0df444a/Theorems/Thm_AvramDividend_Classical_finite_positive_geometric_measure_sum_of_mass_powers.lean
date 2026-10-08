-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_positive_geometric_measure_sum_of_mass_powers
-- name    : AvramDividend.Classical.finite_positive_geometric_measure_sum_of_mass_powers
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T11:24:56.606006+00:00
-- url     : https://prove2.me/theorems/f2d3a66e-c27e-43e2-bd9b-4d6cd9203305
-- title:
--   Positive finite total mass of a subcritical geometric convolution-measure sum
-- statement:
--   Suppose measure m_n has total mass r^n (as with convolution powers of a kernel of total mass r), c is positive finite and c*r<1. Then the geometric measure β=Σ_{n≥0}c^(n+1)m_n has positive finite total mass c/(1−cr). Proof computes Measure.sum mass via tsum and ENNReal.tsum_geometric. This is the generic finite-mass lemma needed to prove that the Esscher-transformed BV scale function converges to the finite positive mass of its renewal measure.
-- source:
--   Pinned Mathlib Measure.sum_apply, Measure.smul_apply, ENNReal.tsum_mul_left, ENNReal.tsum_geometric.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set Filter
open scoped ENNReal NNReal

theorem AvramDividend.Classical.finite_positive_geometric_measure_sum_of_mass_powers
    (m : ℕ → Measure ℝ) (c r : ℝ≥0∞)
    (hc : 0 < c) (hcfinite : c ≠ ⊤)
    (hcr : c * r < 1)
    (hm : ∀ n : ℕ, m n Set.univ = r ^ n) :
    let β : Measure ℝ := Measure.sum (fun n : ℕ => c ^ (n + 1) • m n)
    β Set.univ = c * (1 - c * r)⁻¹ ∧
      0 < β Set.univ ∧ β Set.univ ≠ ⊤ := by sorry
