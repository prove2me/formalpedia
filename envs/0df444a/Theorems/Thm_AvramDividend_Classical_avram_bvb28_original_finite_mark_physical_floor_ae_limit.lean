-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb28_original_finite_mark_physical_floor_ae_limit
-- name    : AvramDividend.Classical.avram_bvb28_original_finite_mark_physical_floor_ae_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T16:33:23.524881+00:00
-- url     : https://prove2.me/theorems/2f235915-8f06-418c-9119-3fcfe7e29569
-- title:
--   Original finite-activity stopped marked floor and continuous mask converge to identical rate almost everywhere
-- statement:
--   Along the literal original BV Lévy source path with no negative marks through the finite horizon, both inclusive-cap negative-mark kernels (uniform frozen-grid and continuous real-time) converge almost everywhere under the true finite-horizon real Lebesgue measure to the same strictly pre-ruin discounted closed-cap rate. Handles arbitrary admissible singular dividends, time-zero right payment, zero/cap reserve contact, ruin and T singleton exceptions. No auxiliary process.
-- source:
--   Proved original physical discounted floor 3ef2e568, strict pre-ruin negative-mark uniform convergence 11fd0ffd, post-ruin eventual floor mask 9ca78cf4, finite-exception 6aaf18d7, contact 70cfb20d and Standing BV; Avram 2007 Prop4(i), (5.13).

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb28_original_finite_mark_physical_floor_ae_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (hFinite : C ≠ ⊤)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) (hMassPos : 0 < X.ν (Iio (0 : ℝ))) (hKernel : ∀ s : Set ℝ, IsCompact s →
      s ⊆ {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C} →
      UniformContinuousOn
        (fun b : ℝ => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν) s)
    (ω : Ω) (hRuinNonzero : ruinTime X x D ω ≠ 0)
    (hSource : ∀ r : ℝ≥0, r ≤ (⟨T, le_of_lt hT⟩ : ℝ≥0) →
      X.X r ω = (r : ℝ) * X.drift) :
    let U : ℝ≥0 → ℝ := fun t =>
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t
    let ψ : ℝ → ℝ := fun b =>
      ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν
    let rate : ℝ≥0 → ℝ := fun t =>
      Real.exp (-(q * (t : ℝ))) * ψ (U t)
    let μ : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal
    let F : ℕ → ℝ → ℝ := fun n r =>
      if 0 ≤ r ∧ r < T * ((n : ℝ) + 1) / ((n : ℝ) + 2) then
        let i : ℕ := ⌊(r / T) * ((n : ℝ) + 2)⌋₊
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
           0 ≤ U (u n i) ∧ ENNReal.ofReal (U (u n i)) ≤ C
        then rate (u n i) else 0
      else 0
    let G : ℕ → ℝ → ℝ := fun n r =>
      let t : ℝ≥0 := Real.toNNReal r
      if 0 < r ∧ r < T - T / ((n : ℝ) + 2) ∧
          (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
          0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
      then rate t else 0
    let f : ℝ → ℝ := fun r =>
      let t : ℝ≥0 := Real.toNNReal r
      if 0 < r ∧ r < T ∧
          (t : ℝ≥0∞) < ruinTime X x D ω ∧
          0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
      then rate t else 0
    (∀ᵐ r ∂((volume : Measure ℝ).restrict (Icc 0 T)),
      Tendsto (fun n => F n r) atTop (𝓝 (f r))) ∧
    (∀ᵐ r ∂((volume : Measure ℝ).restrict (Icc 0 T)),
      Tendsto (fun n => G n r) atTop (𝓝 (f r))) := by sorry
