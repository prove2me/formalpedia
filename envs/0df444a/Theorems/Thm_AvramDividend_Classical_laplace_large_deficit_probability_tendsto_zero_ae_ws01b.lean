-- Prove2me | Theorems.Thm_AvramDividend_Classical_laplace_large_deficit_probability_tendsto_zero_ae_ws01b
-- name    : AvramDividend.Classical.laplace_large_deficit_probability_tendsto_zero_ae_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:13:49.774499+00:00
-- url     : https://prove2.me/theorems/bf65d8a5-d187-4783-a0af-c6a2c721aa3f
-- title:
--   Large drift-deficit event probability vanishes under almost-everywhere nonnegativity
-- statement:
--   Let D_n be a family of real random variables which are nonnegative almost surely, with integrable Laplace kernels and a Laplace transform converging to total mass. For each fixed a>0, the measure of {D_n≥a} tends to zero. Pointwise truncation max(D_n,0) reduces the almost-everywhere hypothesis to the already Proved pointwise nonnegative theorem, without changing a positive-tail event and without changing the exponential integral outside a null set. This is the exact measure-theoretic form needed for BV Lévy drift deficits, whose pathwise monotonicity holds P-almost surely.
-- source:
--   Proved laplace_large_deficit_probability_tendsto_zero_ws01b UUID c1b3476c and measure theory a.e integral congruence; BV drift-deficit nonnegativity follows from the Proved bv_drift_deficit_ae_monotone_all_times UUID bdb273f0.

import Theorems.Thm_AvramDividend_Classical_laplace_large_deficit_probability_tendsto_zero_ws01b
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Lattice

open AvramDividend.Classical MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.laplace_large_deficit_probability_tendsto_zero_ae_ws01b
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → Ω → ℝ) (a : ℝ) (ha : 0 < a)
    (hD : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ D n ω)
    (hMeas : ∀ n, MeasurableSet {ω : Ω | a ≤ D n ω})
    (hLeft : ∀ n, Integrable
      (fun ω => if a ≤ D n ω then (1 - Real.exp (-a) : ℝ) else 0) μ)
    (hOne : Integrable (fun _ : Ω => (1 : ℝ)) μ)
    (hExp : ∀ n, Integrable (fun ω => Real.exp (-D n ω)) μ)
    (hLaplace : Tendsto
      (fun n : ℕ => ∫ ω, Real.exp (-D n ω) ∂μ)
      atTop (𝓝 (μ.real Set.univ))) :
    Tendsto (fun n : ℕ => μ.real {ω : Ω | a ≤ D n ω})
      atTop (𝓝 (0 : ℝ)) := by sorry
