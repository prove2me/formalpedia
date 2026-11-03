-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_void_split_adjacent_horizons
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_void_split_adjacent_horizons
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:50:02.165697+00:00
-- url     : https://prove2.me/theorems/b268c699-c9f3-4ac9-8c5d-3272d82361aa
-- title:
--   Exact intrinsic original-source negative-band void event splits across adjacent time horizons
-- statement:
--   For each path of the actual original spectrally negative Lévy process X and negative jump band, absence of an intrinsic marked jump in (0,T+S] is equivalent to absence in both (0,T] and (T,T+S]. This is pathwise and uses no auxiliary process, law, or independence assumption.
-- source:
--   Source-faithful finite-horizon factorisation supporting the future-increment Poisson zero-count law 390a8092-89ae-45c8-bed8-b43b900baa2f and L² original-filtration programme, mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_void_split_adjacent_horizons
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T S : ℝ≥0) (n : ℕ) :
    (let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
     NX (Ioc 0 (T + S) ×ˢ B) = 0 ↔
       NX (Ioc 0 T ×ˢ B) = 0 ∧
       NX (Ioc T (T + S) ×ˢ B) = 0) := by sorry
