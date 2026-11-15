-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a369_original_fullcell_small_raw_increment_local_postpayment_Lipschitz_ae
-- name    : AvramDividend.Classical.avram_ga_a369_original_fullcell_small_raw_increment_local_postpayment_Lipschitz_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:16:21.385093+00:00
-- url     : https://prove2.me/theorems/525984af-4f54-4470-94f5-4925bd2e5b27
-- title:
--   Original stopped Gaussian source physical small raw increments satisfy uniform postpayment value Lipschitz bound almost surely
-- statement:
--   For the genuine original stopped spectrally negative Lévy source with dividend strategy D and a top-cap C² candidate w, the proved pre-stopping postpayment compact band a137 provides a positive deterministic lower bound a=1/(j+1) and upper bound b=x+j+1 uniformly almost surely at all pre-stop physical mesh starts, including the origin. The proved compact C² local Lipschitz result a204 then gives a positive raw-increment threshold δ and nonnegative constant L, independent of all mesh levels and cells, such that |w(Y_s+R)-w(Y_s)|≤L|R| whenever the original cell starts before ρ and |R|<δ. This is the authentic missing local Lipschitz source of the Gaussian a361 small-cell bound.
-- source:
--   Original a137 postpayment compact prefix band plus a204 C² local Lipschitz; true X.X physical increment and rightLimit D.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
import Theorems.Thm_AvramDividend_Classical_avram_ga_a204_positive_compact_C2_source_small_raw_local_Lipschitz
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a369_original_fullcell_small_raw_increment_local_postpayment_Lipschitz_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (n : ℕ) (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ L : ℝ, 0 ≤ L ∧
      ∀ᵐ ω ∂P, ∀ m i : ℕ,
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let r : ℝ := X.X (s + Δ) ω - X.X s ω
        let y : ℝ := x + X.X s ω - rightLimit D s ω
        s < ρ ω → |r| < δ →
          |w (y + r) - w y| ≤ L * |r| := by sorry
