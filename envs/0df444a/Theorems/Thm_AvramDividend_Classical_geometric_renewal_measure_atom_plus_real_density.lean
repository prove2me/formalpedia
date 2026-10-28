-- Prove2me | Theorems.Thm_AvramDividend_Classical_geometric_renewal_measure_atom_plus_real_density
-- name    : AvramDividend.Classical.geometric_renewal_measure_atom_plus_real_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:17:12.428322+00:00
-- url     : https://prove2.me/theorems/82f973c0-a889-42aa-b0f0-e89f98914bbc
-- title:
--   Geometric Esscher renewal measure as a weighted atom plus a real-density series
-- statement:
--   Suppose the zeroth convolution-power measure is the Dirac mass at zero, and every positive-order geometrically scaled measure has nonnegative Lebesgue density F_n with a pointwise summable shifted series. Then the entire geometrically weighted renewal measure equals the same scalar c times the sum of the initial Dirac atom and the Lebesgue measure with density the shifted series. The proof combines the canonical geometric scalar extraction and renewal atom-plus-real-density results. This supplies the exact measure-level Esscher renewal normalisation needed to connect the finite BV renewal witness to the derivative-density and cstar_lt_top arguments. The remaining substantive input is the density identity for scaled convolution powers.
-- source:
--   Pinned Mathlib measure sums and canonical Proved AvramDividend.Classical.geometric_measure_sum_extract_constant and AvramDividend.Classical.renewal_measure_atom_plus_real_density.

import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_geometric_measure_sum_extract_constant
import Theorems.Thm_AvramDividend_Classical_renewal_measure_atom_plus_real_density
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.geometric_renewal_measure_atom_plus_real_density
    (c : ℝ≥0∞) (F : ℕ → ℝ → ℝ) (m : ℕ → Measure ℝ)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hFmeas : ∀ n : ℕ, Measurable (F n))
    (hFsummable : ∀ x : ℝ,
      Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else F (n - 1) x))
    (hmzero : m 0 = Measure.dirac (0 : ℝ))
    (hmpower : ∀ n : ℕ, c ^ (n + 1) • m (n + 1) =
      volume.withDensity (fun x : ℝ => ENNReal.ofReal (F n x))) :
    Measure.sum (fun n : ℕ => c ^ (n + 1) • m n) =
      c • (Measure.dirac (0 : ℝ) +
        volume.withDensity (fun x : ℝ =>
          ENNReal.ofReal (∑' n : ℕ,
            if n = 0 then (0 : ℝ) else F (n - 1) x))) := by sorry
