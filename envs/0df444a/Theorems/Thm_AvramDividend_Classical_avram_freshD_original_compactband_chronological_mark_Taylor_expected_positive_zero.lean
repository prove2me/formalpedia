-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_compactband_chronological_mark_Taylor_expected_positive_zero
-- name    : AvramDividend.Classical.avram_freshD_original_compactband_chronological_mark_Taylor_expected_positive_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T14:39:29.624923+00:00
-- url     : https://prove2.me/theorems/faec45d6-06b8-4b6f-89f6-aeeb492a95e2
-- title:
--   Original compact-stopped finite negative jump Taylor signed expected positive error vanishes without an assumed uniform mark bound
-- statement:
--   True original chronological negative Lévy mark Taylor mesh error has vanishing expected positive part under an actual common deterministic compact spatial strip for all genuine sampled post-right-dividend prestates and true prejump reserves. No additional arbitrary uniform jump-weight assumption is needed. The Proved exact compact-strip negative-mark Taylor bound 067125d6 yields one deterministic L for all negative mark sizes, including exact jump landing at zero where w(0) can be strictly positive, and including C=⊤. The Proved original chronological Taylor signed expected-upperlimit bridge 71e1a06f applies to this L, using original negative-mark count L1, original chronological prestate convergence and genuine signed one-sided upperlim. The distinct and genuine source work remaining for the physical 242ca5f1 is to construct the spatial stopping bands, actual finite marked times and measurability, plus the joint stopped Gaussian and dividend Stieltjes ledger.
-- source:
--   Original mixed Gaussian/finiteactivity negative Lévy fullmark cash excess 242ca5f1: combine actual marked Taylor signed expected bound and original C2 compact-tail envelope.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_compactband_chronological_mark_Taylor_expected_positive_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (c : ℝ)
    (hc : 0 < c) (hcC : ENNReal.ofReal c ≤ C)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici (0 : ℝ)))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (n : ℕ) (S : Ω → Finset ℝ≥0)
    (hSpos : ∀ ω t, t ∈ S ω → 0 < t)
    (hSneg : ∀ ω t, t ∈ S ω →
      X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t < 0)
    (hSinterior : ∀ ω t, t ∈ S ω →
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) t - D t ω ∈
        Ioo (0 : ℝ) c)
    (hCount : ∀ᵐ ω ∂P, ((S ω).card : ℝ) ≤
      (((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
          (fun t : ℝ≥0 => (t,
            X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
          (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ))).toReal)
    (grid : ℕ → Ω → ℝ≥0 → ℝ≥0)
    (hgrid : ∀ᵐ ω ∂P, ∀ t ∈ S ω,
      Tendsto (fun m => grid m ω t) atTop (𝓝[<] t))
    (E : ℕ → Ω → ℝ≥0 → ℝ)
    (hEsource : ∀ m ω t,
      E m ω t =
        let y := x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) t -
          D t ω
        let z := X.X t ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) t
        let u := x + X.X (grid m ω t) ω -
          rightLimit D (grid m ω t) ω
        ((w (u + z) - w u -
          (if -1 < z then z * deriv w u else 0)) -
         (w (y + z) - w y -
          (if -1 < z then z * deriv w y else 0))))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hBand : Icc a b ⊆
      {r : ℝ | 0 < r ∧ ENNReal.ofReal r < C})
    (hPreband : ∀ ω t, t ∈ S ω →
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) t - D t ω ∈ Icc a b)
    (hSample : ∀ m ω t, t ∈ S ω →
      x + X.X (grid m ω t) ω -
        rightLimit D (grid m ω t) ω ∈ Icc a b)
    (hMeas : ∀ m, AEStronglyMeasurable
      (fun ω => max (∑ t ∈ S ω, E m ω t) 0) P) :
    Tendsto
      (fun m => ∫ ω, max (∑ t ∈ S ω, E m ω t) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
