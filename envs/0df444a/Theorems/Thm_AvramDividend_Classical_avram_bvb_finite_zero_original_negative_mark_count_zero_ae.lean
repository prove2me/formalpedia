-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_finite_zero_original_negative_mark_count_zero_ae
-- name    : AvramDividend.Classical.avram_bvb_finite_zero_original_negative_mark_count_zero_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:03:17.387197+00:00
-- url     : https://prove2.me/theorems/e55c6019-f720-4d3c-b0c3-3cfd18fab3ef
-- title:
--   Zero negative-jump intensity makes every bounded-horizon original negative-mark count vanish almost surely
-- statement:
--   For every fixed T, the original negative marked jump point measure has mass zero almost surely on (0,T] times negative marks. Deduce from Proved exact expected count and original count measurability; no finite cap or dividend assumptions.
-- source:
--   Uses Proved 0d444e07 (original expected count exact) and 5cb1e247 (original marked count measurable) plus lintegral_eq_zero_iff. Needed to prove zero-intensity path aaac3cb1 and original cash ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_finite_zero_original_negative_mark_count_zero_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hZero : X.ν (Iio (0 : ℝ)) = 0) (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0 := by sorry
