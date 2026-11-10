-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_excess28_original_fullmark_uniform_width_L1_vanish
-- name    : AvramDividend.Classical.avram_bv_excess28_original_fullmark_uniform_width_L1_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:45:16.267738+00:00
-- url     : https://prove2.me/theorems/fbf40631-9be7-49f6-802e-44a01f51e3d6
-- title:
--   Original finite-BV full negative-jump intensity gives vanishing expected uniform-mesh occupied width
-- statement:
--   For the actual original BV Levy source with finite negative-jump intensity, the expected full-horizon original jump count times 1/(n+2) tends to zero. This supplies the second zero-contact positive error in Proved f3f336fd, after Proved 32f0b234 handles jump collisions. No arbitrary-grid convergence or separate generator B L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_excess28_original_fullmark_uniform_width_L1_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    Filter.Tendsto (fun n : ℕ => ∫⁻ ω,
      (((n + 2 : ℕ) : ℝ≥0∞)⁻¹) * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by sorry
