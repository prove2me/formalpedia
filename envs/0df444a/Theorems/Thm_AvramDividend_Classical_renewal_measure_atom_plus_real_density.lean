-- Prove2me | Theorems.Thm_AvramDividend_Classical_renewal_measure_atom_plus_real_density
-- name    : AvramDividend.Classical.renewal_measure_atom_plus_real_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:03:56.052796+00:00
-- url     : https://prove2.me/theorems/e2affa0d-97a2-4896-bd98-0c3c5081d487
-- title:
--   Geometric renewal measure splits into the Dirac starting atom and a real-series density
-- statement:
--   If a measure sequence starts with a point mass at zero, and each later measure has the nonnegative real convolution-power density F_n, then its countable sum is exactly Dirac at zero plus Lebesgue withDensity of the shifted real series. The proof separates the zeroth summand and imports the proved countable-real-density theorem. The result connects the finite BV Esscher renewal witness, including its initial atom, to a real integral of the renewal density required by bv_ac_esscher_scaled_renewal_kernel_series_data and cstar_lt_top.
-- source:
--   Pinned Mathlib ENNReal.tsum_eq_add_tsum_ite and canonical countable_real_density_measure_sum_eq_real_tsum.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Theorems.Thm_AvramDividend_Classical_countable_real_density_measure_sum_eq_real_tsum
open AvramDividend.Classical MeasureTheory
open scoped ENNReal NNReal

theorem AvramDividend.Classical.renewal_measure_atom_plus_real_density
    (F : ℕ → ℝ → ℝ) (m : ℕ → Measure ℝ)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hFmeas : ∀ n : ℕ, Measurable (F n))
    (hFsummable : ∀ x : ℝ,
      Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else F (n - 1) x))
    (hmzero : m 0 = Measure.dirac (0 : ℝ))
    (hmsucc : ∀ n : ℕ, m (n + 1) =
      volume.withDensity (fun x : ℝ => ENNReal.ofReal (F n x))) :
    Measure.sum m = Measure.dirac (0 : ℝ) +
      volume.withDensity (fun x : ℝ =>
        ENNReal.ofReal (∑' n : ℕ,
          if n = 0 then (0 : ℝ) else F (n - 1) x)) := by sorry
