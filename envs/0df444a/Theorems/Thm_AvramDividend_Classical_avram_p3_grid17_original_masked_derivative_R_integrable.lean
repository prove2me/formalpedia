-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid17_original_masked_derivative_R_integrable
-- name    : AvramDividend.Classical.avram_p3_grid17_original_masked_derivative_R_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T21:56:49.356188+00:00
-- url     : https://prove2.me/theorems/ab781d06-2007-437b-a1a8-abde0400f456
-- title:
--   Original stopped BV derivative-weighted physical residual is integrable on a coefficient-bounded measurable event
-- statement:
--   For the canonical original pre-dividend left-limit reserve, original stopped coefficient exp(-q t) * deriv w and authentic BV drift-minus-jump residual R, the finite physical weighted sum is integrable when restricted to an arbitrary measurable event on which these actual coefficients are uniformly bounded. Unlike the globally bounded derivative lemma, this allows pathwise adaptive finite-row masks. It is a direct consequence of Proved stopped-derivative measurability 13fbd165 and the event-local residual theorem b02d05bb, preserving the original process and finite grid.
-- source:
--   Original-process closure bridge for canonical P3 0b2da5b3. Imports public Proved 13fbd165 and proposed event-local R theorem b02d05bb (proof candidate 31393 pending at proposal time).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_nonint_original_masked_derivative_grid_cell_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid17_original_event_local_BV_weighted_residual_integrable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid17_original_masked_derivative_R_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      (u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (n : ℕ) (S : ℝ≥0) (hS : u n (n + 1) ≤ S)
    (s : Set Ω) (hs : MeasurableSet s) (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ ω ∈ s, ∀ i < n + 1,
      |(if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Function.leftLim (fun t : ℝ≥0 =>
              x + X.X t ω - rightLimit D t ω) (u n i) ∧
            ENNReal.ofReal (Function.leftLim (fun t : ℝ≥0 =>
              x + X.X t ω - rightLimit D t ω) (u n i)) < C then
          Real.exp (-(q * (u n i : ℝ))) *
            deriv w (Function.leftLim (fun t : ℝ≥0 =>
              x + X.X t ω - rightLimit D t ω) (u n i))
        else 0)| ≤ K) :
    Integrable (fun ω => if ω ∈ s then
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0)
      ∑ i ∈ Finset.range (n + 1),
        (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
        else 0) * (R (u n i) - R (u n (i + 1)))
    else 0) P := by sorry
