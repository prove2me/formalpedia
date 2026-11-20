-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_true_preruin_uniform_caplinear_full_cash
-- name    : AvramDividend.Classical.avram_pj_workerC_true_preruin_uniform_caplinear_full_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T21:53:57.071772+00:00
-- url     : https://prove2.me/theorems/303bb614-fc02-4f3d-a4b0-07179a00960e
-- title:
--   Exact strictly preruin uniformly clipped physical-grid caplinear discounted full-dividend Stieltjes cash bound
-- statement:
--   On any actual sample path strictly before ruin, the uniform grid min(i t/(m+1),t) has monotone successive times and all endpoint post-dividend reserves remain preruin. The proved original full Stieltjes terminal cash inequality applies automatically without a separately assumed monotone grid or survival at endpoints. Keeps entire within-cell dividends rather than only right-jump atoms.
-- source:
--   Specialises Proved 6e0125db with genuine uniform preterminal grid and automatically discharged survival for all cells; independent of Gaussian and finite intensity, supports Worker C source-level signed ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_original_controlled_leftclock_full_stieltjes_terminal_reward_grid_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_true_preruin_uniform_caplinear_full_cash
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
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω)
    (m : ℕ) :
    let u : ℕ → ℝ≥0 := fun i =>
      min (((i : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) * t) t
    let E : ℝ≥0 → ℝ := fun s => Real.exp (-(q * (s : ℝ)))
    let Y : ℝ≥0 → ℝ := fun s => x + X.X s ω - rightLimit D s ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    E (u (m + 1)) * V (Y (u (m + 1))) +
      (∫⁻ s in Icc (0 : ℝ) ((u (m + 1)) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ≤
      V x +
        ∑ i ∈ Finset.range (m + 1),
          ((E (u (i + 1)) - E (u i)) * V (Y (u (i + 1))) +
            E (u i) * (V (Z i) - V (Y (u i)))) := by sorry
