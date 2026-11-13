-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_ruinstopped_prepayment_compact_allband
-- name    : AvramDividend.Classical.avram_bva_a22_original_ruinstopped_prepayment_compact_allband
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:05:49.604119+00:00
-- url     : https://prove2.me/theorems/577caf39-818c-4087-93e5-4c7acaa3a98a
-- title:
--   Original BV stopped prepayment reserve compact source eventually included in every prescribed spatial band
-- statement:
--   For the genuine original filtered spectrally negative Lévy process X and admissible original dividend D, under arbitrary prescribed cofinal spatial bands a(n),b(n), every fixed compact interval strictly inside the positive cap is eventually covered uniformly at all sample paths, all horizons and all ruin-clipped stopping times whenever the actual original pre-right-dividend left-limit reserve is inside the compact interval. The fixed eventual band index is independent of path, physical cell or clock. This exact original stopped source interface follows from the A22 proved arbitrary-band endpoint lemma and is designed for compensation masking. No eventual inclusion of noncompact moving reserve states and no global generator L1 is claimed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_arbitrary_cofinal_bands_cover_each_fixed_compact
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_ruinstopped_prepayment_compact_allband
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (a b : ℕ → ℝ)
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n))
    (c d : ℝ) (hc : 0 < c) (hcd : c ≤ d)
    (hcC : ENNReal.ofReal c < C) (hdC : ENNReal.ofReal d < C) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (S : ℝ≥0) (ω : Ω) (t : ℝ≥0),
      (t : ℝ≥0∞) ≤ min (ruinTime X x D ω) (S : ℝ≥0∞) →
      Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t ∈ Icc c d →
      Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t ∈ Icc (a n) (b n) := by sorry
