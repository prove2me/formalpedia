-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger109_monotone_finite_cell_real_mass_partition
-- name    : AvramDividend.Classical.avram_gledger109_monotone_finite_cell_real_mass_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:23:29.489135+00:00
-- url     : https://prove2.me/theorems/cb092401-ac08-4490-9b4e-67e85f7e21b4
-- title:
--   Finite original grid cell masses add exactly after real conversion
-- statement:
--   For any monotone real mesh and locally finite Stieltjes measure on its full half-open span, the real-valued measure masses of every interior cell sum to precisely the mass of their union. This permits the original-process gledger99 mesh-rate sum to be bounded by a single clipped strict cash envelope, with no overcounting.
-- source:
--   Original gledger81 pathwise interior sum uses ∑ q Δ * μ(Ioc cell).toReal. Proved gledger88 supplies the ENNReal cell partition; this child transfers it to a finite real-valued sum. This is a strictly smaller algebra/measure leaf and has no stochastic expectations.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger88_monotone_grid_Ioc_cash_exact_partition
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger109_monotone_finite_cell_real_mass_partition
    (μ : Measure ℝ) (v : ℕ → ℝ) (hv : Monotone v) (k : ℕ)
    (hfinite : μ (Ioc (v 0) (v k)) < ⊤) :
    (∑ i ∈ Finset.range k,
      (μ (Ioc (v i) (v (i + 1)))).toReal) =
      (μ (Ioc (v 0) (v k))).toReal := by sorry
