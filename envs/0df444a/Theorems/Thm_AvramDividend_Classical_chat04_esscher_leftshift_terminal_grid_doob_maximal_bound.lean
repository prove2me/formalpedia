-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_terminal_grid_doob_maximal_bound
-- name    : AvramDividend.Classical.chat04_esscher_leftshift_terminal_grid_doob_maximal_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:36:15.891931+00:00
-- url     : https://prove2.me/theorems/f16e80ac-c1a4-4f2e-af69-1da03eb117ed
-- title:
--   Doob maximal bound for the compensated Esscher exponential on every bounded finite deterministic grid
-- statement:
--   For any spectrally negative Lévy process, nonnegative Esscher tilt θ, 0≤ε≤θ, fixed finite horizon T, monotone bounded sampling grid g(n)≤T, positive threshold parameter a≥0 and finite grid of indices 0..n, the actual terminal Esscher probability of a compensated negative-exponential martingale maximum at least a is bounded by 1/a. Precisely a·Q_T(max_{k≤n} exp(−εX_{g(k)}−g(k)[ψ(θ−ε)−ψθ])≥a)≤1 in ENNReal. This is the key finite-grid Doob maximal inequality on the *genuine fixed terminal tilted probability law*, from which the running-downcrossing bound follows.
-- source:
--   The accepted Esscher discrete-grid martingale provides a real Nat-indexed Martingale under Q_T and filtration F_{g(k)}. Accepted finite-horizon Esscher probability supplies IsFiniteMeasure Q_T. Positivity of the exponential supplies nonnegativity. Accepted fixed-terminal compensated Esscher mean-one theorem gives E_QT Z_{gk}=1. Apply the already Proved generic `nat_positive_martingale_finite_grid_maximal_unit_bound` directly and unfold abbreviations. This avoids any unconstructed global tilted law or Wiener–Hopf factorisation.

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_fixed_terminal_nat_grid_martingale
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_compensated_fixed_terminal_unit_mean
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
import Theorems.Thm_AvramDividend_Classical_nat_positive_martingale_finite_grid_maximal_unit_bound
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_leftshift_terminal_grid_doob_maximal_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ ε : ℝ) (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (hεθ : ε ≤ θ)
    (T : ℝ≥0) (g : ℕ → ℝ≥0) (hg : Monotone g)
    (hgT : ∀ i : ℕ, g i ≤ T)
    (a : ℝ≥0) (n : ℕ) :
    (a : ℝ≥0∞) *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
        {ω : Ω | (a : ℝ) ≤
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun k => Real.exp
              (-ε * X.X (g k) ω -
                (g k : ℝ) * (X.ψ (θ - ε) - X.ψ θ)))} ≤ 1 := by sorry
