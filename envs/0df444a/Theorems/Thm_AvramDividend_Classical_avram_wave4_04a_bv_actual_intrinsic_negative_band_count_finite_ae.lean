-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_negative_band_count_finite_ae
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_negative_band_count_finite_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:37:14.536001+00:00
-- url     : https://prove2.me/theorems/549cc71d-d7e3-4916-bdac-1c5fd9877053
-- title:
--   Actual BV original Lévy intrinsic jump-count measure is finite on every separated negative band rectangle
-- statement:
--   For a bounded-variation original spectrally negative Lévy source, the actual path intrinsic counting measure N_X(ω) obtained by restricting time counting measure to genuine positive nonzero jump times and mapping u to (u,ΔX_u(ω)) has finite mass almost surely on (0,T]×(-∞,-ε] for each finite horizon T and threshold ε>0. This is derived from the precise source rectangle counting-measure identity and a genuine source finite set of downward jumps larger than ε. It is the original X itself, not a constructed equal-law Lévy process, and proves only BV band local finiteness, not Poisson laws or predictable compensation.
-- source:
--   Canonical Proved original-path intrinsic rectangle Set.encard identity f6336d40-2d19-444f-bacd-83724316de67 and newly authored (awaiting canonical Proved) source BV finite truncated negative jump times 69d28cd1-ae1f-4bee-a05d-eccb3bbd314f; Mathlib finite Set.encard, coercion to ENNReal. Do not prove/import until dependency is accepted.

import Mathlib.Data.Set.Card
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_truncated_negative_jump_times_finite_ae

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_negative_band_count_finite_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (T : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ ω ∂P,
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-ε)) < ⊤ := by sorry
