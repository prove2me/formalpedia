-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_full_stieltjes_grid_budget
-- name    : AvramDividend.Classical.avram_bvb_topcap_original_full_stieltjes_grid_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:27:12.134201+00:00
-- url     : https://prove2.me/theorems/da858639-84df-455d-8847-55ab90ccc4e3
-- title:
--   Original top-cap finite activity BV discounted Stieltjes payment and terminal grid bound
-- statement:
--   On every source original-process pre-ruin increasing clock grid, the discounted postpayment terminal value plus full discounted original dividend Stieltjes measure up to that clock is dominated by initial w(x) plus the exact nonpayment spatial and discount increments. Cap equals top, allowing the transformed value V in the generic source theorem to equal w exactly.
-- source:
--   Direct source-faithful C=top specialisation of Proved avram_wave5_03_actual_original_controlled_leftclock_full_stieltjes_terminal_reward_grid_bound, theorem 6e0125db. Handles source original time-zero and all continuous/singular dividend payments without a finite cap; useful physical ledger atom for 28336ae5.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_global_real_signed_stieltjes_grid_nonpos

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bvb_topcap_original_full_stieltjes_grid_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (hCapTop : C = ⊤) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
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
    E (u n) * w (Y (u n)) +
      (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ≤
      w x +
        ∑ i ∈ Finset.range n,
          ((E (u (i + 1)) - E (u i)) * w (Y (u (i + 1))) +
            E (u i) * (w (Z i) - w (Y (u i)))) := by sorry
