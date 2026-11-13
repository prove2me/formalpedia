-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb30_original_finite_mark_floor_uniform_signed_bound
-- name    : AvramDividend.Classical.avram_bvb30_original_finite_mark_floor_uniform_signed_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T16:46:36.392856+00:00
-- url     : https://prove2.me/theorems/b2e67b7e-8abc-496b-b993-f1953898af36
-- title:
--   Original finite-cap signed negative-mark rate uniformly bounded along physical real-time and floor masks
-- statement:
--   On the true original finite-activity BV Lévy source with the same admissible dividend path, every physical floor frozen negative-mark rate and every continuously masked rate is bounded by one deterministic nonnegative constant. Derives directly from compact-cap uniform continuity of the genuine mark-integrated loss, the positive discount and both original masks, including zero and upper cap and ruin.
-- source:
--   Original Proved finite cap original mark kernel bound 2fd66d45, positive discount Real.exp, Avram et al 2007 Prop 4(i),(5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva20_original_closed_cap_mark_kernel_uniform_bound
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb30_original_finite_mark_floor_uniform_signed_bound
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
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ n r, ‖F n r‖ ≤ B) ∧
      (∀ n r, ‖G n r‖ ≤ B) := by sorry
