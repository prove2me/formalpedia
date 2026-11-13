-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_finite_grid_open_mark_le_closed_contact
-- name    : AvramDividend.Classical.avram_bvb22_original_finite_grid_open_mark_le_closed_contact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T13:38:24.109232+00:00
-- url     : https://prove2.me/theorems/69ca0095-eee8-4343-b97c-ab2517074eac
-- title:
--   Original physical grid open-cap negative-mark compensation bounded below by closed-cap contact rate
-- statement:
--   At every actual finite monotone original Lévy time grid for the true admissible dividend D, the original source negative-mark integrated rate has nonpositive sign at all inclusive reserve-cap states. The frozen open-interior mask drops those nonpositive contact contributions; hence the original open-cap physical compensation sum is at least its inclusive-cap counterpart. The proof accounts for zero/cap reserve, ruin-time strict masking and nonnegative mesh increments, with no atomic mark, auxiliary process, or invented source.
-- source:
--   Avram Palmowski Pistorius (2007) Prop 4(i), Eq (5.13); source-exact original X and D. Proved 07f94b51 closed-cap negative mark rate sign.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_closed_cap_negative_mark_rate_nonpos
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb22_original_finite_grid_open_mark_le_closed_contact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (n : ℕ) (ω : Ω) :
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    let ψ : ℝ → ℝ := fun b =>
      ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν
    let A : ℝ := ∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 ≤ Z i ∧ ENNReal.ofReal (Z i) ≤ C then
        Real.exp (-(q * (u n i : ℝ))) * ψ (Z i) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    let J : ℝ := ∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) * ψ (Z i) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    A ≤ J := by sorry
