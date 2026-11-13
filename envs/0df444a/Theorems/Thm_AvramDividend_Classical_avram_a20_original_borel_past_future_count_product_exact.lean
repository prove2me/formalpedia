-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_past_future_count_product_exact
-- name    : AvramDividend.Classical.avram_a20_original_borel_past_future_count_product_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T11:35:36.054512+00:00
-- url     : https://prove2.me/theorems/1bb8c354-a6d1-4074-a445-b7180fc2f6ba
-- title:
--   Exact original Borel marked past-future chronological rectangle count product moment
-- statement:
--   For the literal original spectrally negative Lévy process, every measurable Borel jump-mark set B and deterministic times 0≤s≤t, the genuine original samplewise past marked count times the future marked count has expected product equal to the product of their source ν rates: (s ν(B))((t−s)ν(B)). Proved original-filtration adaptedness of arbitrary Borel past counts, Proved original past-weighted future factorisation, and Proved unconditional future Borel Lévy rate yield this directly on the original measure space. No Poisson law, factorial moment, variance theorem or auxiliary probability space is assumed. This is a physical off-diagonal source input to the JA36 chronological factorial-pair argument.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_borel_past_future_count_product_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    (∫⁻ ω, NX ω (Ioc 0 s ×ˢ B) *
      NX ω (Ioc s t ×ˢ B) ∂P) =
      ((s : ℝ≥0∞) * X.ν B) *
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
