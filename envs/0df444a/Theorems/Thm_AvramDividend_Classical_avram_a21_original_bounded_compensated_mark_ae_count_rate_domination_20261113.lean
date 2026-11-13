-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_bounded_compensated_mark_ae_count_rate_domination_20261113
-- name    : AvramDividend.Classical.avram_a21_original_bounded_compensated_mark_ae_count_rate_domination_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:27:00.565476+00:00
-- url     : https://prove2.me/theorems/380e3c66-6d63-44a3-8774-1659019e7327
-- title:
--   Original bounded Borel compensated marked jump integral dominated by exact source count and finite compensator
-- statement:
--   Under original finite negative Lévy activity and bounded measurable real marks, the genuine compensated original marked jump integral on any negative Borel strip has absolute value bounded almost surely by the original physical marked jump count plus its exact Lévy compensator intensity.
-- source:
--   Proved physical original marked bounded-integral count domination d8f940f9 and new finite original Borel mark intensity bound 1425b5d5. The squared count-plus-compensator source envelope was already Proved 7413b910; this finishes the explicit domination clause for 67336b2d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_mark_integral_ae_count_domination
import Theorems.Thm_AvramDividend_Classical_avram_a21_finite_borel_mark_real_intensity_norm_bound_20261113
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_bounded_compensated_mark_ae_count_rate_domination_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Set ℝ) (hS : MeasurableSet S)
    (hNeg : S ⊆ Iio (0 : ℝ))
    (f : ℝ → ℝ) (hf : Measurable f)
    (hBound : ∀ z ∈ S, |f z| ≤ 1) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let N : Ω → ℝ := fun ω => (NX ω (Ioc 0 T ×ˢ S)).toReal
    let r : ℝ := ((T : ℝ≥0∞) * X.ν S).toReal
    ∀ᵐ ω ∂P,
      ‖(∫ p in (Ioc 0 T ×ˢ S), f p.2 ∂NX ω) -
        (T : ℝ) * (∫ z in S, f z ∂X.ν)‖ ≤ N ω + r := by sorry
