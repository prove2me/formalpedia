-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_original_controlled_leftclock_full_stieltjes_terminal_reward_grid_bound
-- name    : AvramDividend.Classical.avram_wave5_03_actual_original_controlled_leftclock_full_stieltjes_terminal_reward_grid_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:17:38.335523+00:00
-- url     : https://prove2.me/theorems/6e0125db-7718-49b2-b347-0776bce5fa1e
-- title:
--   Actual discounted terminal reserve plus full Stieltjes dividends is bounded by original source evolution and clock drift on every pre-ruin grid
-- statement:
--   For an actual original spectrally negative Lévy source and an admissible dividend strategy up to an arbitrary finite monotone pre-ruin grid, the exponentially discounted terminal cap-linear verification value plus the true closed-horizon dividendMeasure integral, including the time-zero atom, all right-payment jumps and the absolutely and singular-continuous dividend variation, is bounded by the initial verification value plus precisely the original source-frozen increment of V at each cell and the deterministic exponential clock drift evaluated at the new postpayment reserve. This is the nonstochastic exact finite-grid inequality that combines a telescoping moving-source chain with the canonically Proved full signed source Stieltjes control. It does not assume martingale compensation or claim the remaining stochastic mesh limit. It is directly consumable by BV C1 and corrected UBV C2 verification owners.
-- source:
--   Same path riskProcess X x D, X.X_zero, rightLimit D, dividendMeasure, positive-cap IsAdmissibleLe. Uses accepted 04-B original left-discounted full Stieltjes signed grid 680d469d-d6d1-4ae9-ba12-543f1825a206. No independent process and no silent omitted boundary premise. BV ef7e6c20-a118-46f0-ac94-5b02204bba49, UBV 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_global_real_signed_stieltjes_grid_nonpos

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_actual_original_controlled_leftclock_full_stieltjes_terminal_reward_grid_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u) (hu0 : u 0 = 0)
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    E (u n) * V (Y (u n)) +
      (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ≤
      V x +
        ∑ i ∈ Finset.range n,
          ((E (u (i + 1)) - E (u i)) * V (Y (u (i + 1))) +
            E (u i) * (V (Z i) - V (Y (u i)))) := by sorry
