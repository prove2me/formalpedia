-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_countable_simple_pathwise
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_intrinsic_countable_simple_pathwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:31:12.128635+00:00
-- url     : https://prove2.me/theorems/2bbac71e-ddd6-42a8-afa6-810b47a061f6
-- title:
--   Original Lévy samplewise countable predictable-simple jump integral equals weighted intrinsic counts
-- statement:
--   On each fixed sample ω of the genuine original spectrally negative Lévy process X, the integral with respect to the original intrinsic marked jump measure of a countable sum of deterministic marked-rectangle indicator functions, with arbitrary nonnegative sample-dependent coefficients H_i(ω), is exactly the countable sum of H_i(ω) times the original marked-jump measure of each rectangle. The equality holds pathwise without mark-rectangle disjointness, event-rate assumptions, ν identification, or integrability restrictions; it is the deterministic bridge needed to turn P2-E predictable simple stochastic integrands into literal source jump counts.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_tsum, lintegral_indicator and original source jump measure definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_intrinsic_countable_simple_pathwise
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ι → ℝ≥0) (B : ι → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (H : ι → Ω → ℝ≥0∞) (ω : Ω) :
    (∫⁻ p, ∑' i, (Ioc (s i) (t i) ×ˢ B i).indicator (fun _ => H i ω) p ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ∑' i, H i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc (s i) (t i) ×ˢ B i) := by sorry
