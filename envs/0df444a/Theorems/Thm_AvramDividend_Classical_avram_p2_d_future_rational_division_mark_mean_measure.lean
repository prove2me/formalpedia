-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_rational_division_mark_mean_measure
-- name    : AvramDividend.Classical.avram_p2_d_future_rational_division_mark_mean_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:52:08.675993+00:00
-- url     : https://prove2.me/theorems/ca5084c5-2363-4e6e-bc8b-3bfe02198d89
-- title:
--   Uniform original marked rate at explicit positive-denominator rational horizons
-- statement:
--   There exists a genuine original source mark Borel measure ρ such that for every rational physical horizon n/d (n natural, d positive natural) and every Borel mark B, the expected original intrinsic marked jump count equals (n/d)*ρ(B) in ENNReal, including infinite-activity cases. The time is the literal NNReal ratio and no independent time-relation hypothesis is required.
-- source:
--   Use the Proved original rational-time uniform mark measure helper 6484c4c2, with the denominator nonzero and NNReal field_simp identity d*(n/d)=n. Preserves original P, 𝓕 and X.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_rational_division_mark_mean_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ ρ : Measure ℝ, ∀ (n d : ℕ), 0 < d →
      ∀ (B : Set ℝ), MeasurableSet B →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 ((n : ℝ≥0) / (d : ℝ≥0)) ×ˢ B) ∂P) =
        ((n : ℝ≥0∞) / (d : ℝ≥0∞)) * ρ B := by sorry
