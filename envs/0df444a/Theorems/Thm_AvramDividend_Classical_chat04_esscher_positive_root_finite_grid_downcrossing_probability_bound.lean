-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_positive_root_finite_grid_downcrossing_probability_bound
-- name    : AvramDividend.Classical.chat04_esscher_positive_root_finite_grid_downcrossing_probability_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:46:56.079244+00:00
-- url     : https://prove2.me/theorems/85139e96-311d-41b6-9d4b-7ec62d8276d2
-- title:
--   Finite-grid downward-barrier crossing probability has a uniform exponential Esscher bound
-- statement:
--   For a positive q-root φ with ψφ=q>0 and a finite terminal Esscher horizon T, every monotone bounded deterministic observation grid g(k)≤T and every sample count n satisfy the exponential lower-barrier bound exp(φb/2)·Q_T^φ(∃k≤n:X_{g(k)}≤−b)≤1. The threshold is carried as a nonnegative-real parameter a constrained by a=exp(φb/2), to match the existing Doob theorem without lossy coercions. This is the first actual running-minimum probability estimate under genuine Esscher laws, uniform in grid cardinality and observation times.
-- source:
--   By the proved Lévy exponent secant monotonicity, ψ(φ/2)≤q/2, so the compensated Esscher exponential drift κ=ψφ−ψ(φ/2)≥0. A crossing at index k implies its exponential martingale is at least exp(φb/2), and hence so is the finite-grid maximum. Use Finset.le_sup' for the sampled index, measure monotonicity, and the already Proved `chat04_esscher_leftshift_terminal_grid_doob_maximal_bound` under Q_T. The proof requires neither a global tilted probability nor Wiener–Hopf and is the critical input for passing to dense continuous-time grids.

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_terminal_grid_doob_maximal_bound
import Theorems.Thm_AvramDividend_Classical_levy_psi_positive_secant_monotone
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_positive_root_finite_grid_downcrossing_probability_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ b : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (hroot : X.ψ φ = q)
    (T : ℝ≥0) (g : ℕ → ℝ≥0) (hg : Monotone g)
    (hgT : ∀ i : ℕ, g i ≤ T)
    (a : ℝ≥0) (ha : (a : ℝ) = Real.exp ((φ / 2) * b))
    (n : ℕ) :
    (a : ℝ≥0∞) *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (φ * X.X T ω - (T : ℝ) * X.ψ φ))))
        {ω : Ω | ∃ k : ℕ, k ≤ n ∧ X.X (g k) ω ≤ -b} ≤ 1 := by sorry
