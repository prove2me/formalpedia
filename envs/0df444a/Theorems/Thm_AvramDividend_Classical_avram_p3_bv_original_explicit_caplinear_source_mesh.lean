-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_explicit_caplinear_source_mesh
-- name    : AvramDividend.Classical.avram_p3_bv_original_explicit_caplinear_source_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T19:54:34.058196+00:00
-- url     : https://prove2.me/theorems/dca893c2-0022-41e3-87cf-0dded3132ec5
-- title:
--   Original controlled BV physical source grid with automatic positive-cap linear verification extension
-- statement:
--   For the actual spectrally negative Lévy process X and original admissible dividend control D at every positive finite or infinite cap, the explicit cap-linear extension of any interior C1 HJB candidate yields the true finite chronological discounted source-grid inequality. The exact original closed Stieltjes dividend measure includes the time-zero atom, all right payments and continuous/singular-continuous mass. Both cap-extension properties are constructed, not assumed. This is a deterministic finite-grid pathwise accounting lemma, not a completed stochastic verification.
-- source:
--   Source-exact specialization of Proved AvramDividend.Classical.avram_wave5_03_actual_original_controlled_leftclock_full_stieltjes_terminal_reward_grid_bound (6e0125db).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_original_controlled_leftclock_full_stieltjes_terminal_reward_grid_bound

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- Exact physical X/D source grid, with the cap-linear extension
constructed rather than assumed. Cash includes the time-zero atom. -/

theorem AvramDividend.Classical.avram_p3_bv_original_explicit_caplinear_source_mesh
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u) (hu0 : u 0 = 0)
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    E (u n) * V (Y (u n)) +
      (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal ≤
      V x +
        ∑ i ∈ Finset.range n,
          ((E (u (i + 1)) - E (u i)) * V (Y (u (i + 1))) +
            E (u i) * (V (Z i) - V (Y (u i)))) := by sorry
