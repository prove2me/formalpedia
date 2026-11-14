-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_void_negative_mark_annulus_from_physical_event_20261114
-- name    : AvramDividend.Classical.avram_a27_original_void_negative_mark_annulus_from_physical_event_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:48:28.072642+00:00
-- url     : https://prove2.me/theorems/794fe958-b328-44d8-b4c6-0c3a5193bcc2
-- title:
--   Original finite-activity physical marked-jump measure vanishes eventually on all shrinking omitted annuli under Borel source mark map
-- statement:
--   For a finite-activity original spectrally negative Levy source with measurable physical marked path map, on one conull event every horizon eventually has zero marked negative-jump measure in the omitted shrinking band.
-- source:
--   A26 original all-horizons no tiny negative marks and A27 marked pushforward disjoint support zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source absence of omitted negative marks implies exactly zero physical marked-jump measure on every shrinking annulus. -/

theorem AvramDividend.Classical.avram_a27_original_void_negative_mark_annulus_from_physical_event_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hMark : ∀ ω : Ω,
      Measurable (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      ∃ N : ℕ, ∀ n ≥ N,
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Ioo (-(1 / ((n : ℝ) + 1))) (0 : ℝ)) = 0 := by sorry
