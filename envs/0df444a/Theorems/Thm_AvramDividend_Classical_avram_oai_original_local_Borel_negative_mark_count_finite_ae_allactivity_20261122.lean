-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_original_local_Borel_negative_mark_count_finite_ae_allactivity_20261122
-- name    : AvramDividend.Classical.avram_oai_original_local_Borel_negative_mark_count_finite_ae_allactivity_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:44:24.469482+00:00
-- url     : https://prove2.me/theorems/f256079c-bf6e-442f-81e9-b50a0a2942db
-- title:
--   Actual all-activity spectrally negative Lévy marked negative Borel jump count is finite almost surely on every bounded time interval when local Lévy intensity is finite
-- statement:
--   For the ACTUAL original intrinsic marked Lévy jump measure NX, any Borel negative mark set B with finite local Lévy intensity ν(B), and any finite interval [s,t], prove its physical number of jumps NX((s,t]×B) is finite P-almost surely, even if ν((−∞,0))=∞. This follows rigorously from the already Proved actual Lévy marked Campbell lintegral identity (expected count=(t−s)ν(B)<∞), actual physical marked rectangle measurability and Mathlib ae_lt_top. This is the essential all-activity finite-count source needed to lift ENNReal marked interval additivity to exact REAL finite-count process increments, and ultimately prove the original physical simple compensated-mark process is a genuine right-continuous-filtration martingale.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_negative_Borel_marked_Poisson_interval_Campbell_exact
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_original_local_Borel_negative_mark_count_finite_ae_allactivity_20261122
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : B ⊆ Iio (0 : ℝ)) (hν : X.ν B < ⊤) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ∀ᵐ ω ∂P, NX ω (Ioc s t ×ˢ B) < ⊤ := by sorry
