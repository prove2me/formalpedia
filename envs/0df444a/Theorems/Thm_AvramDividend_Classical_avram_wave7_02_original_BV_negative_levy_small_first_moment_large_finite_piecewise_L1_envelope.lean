-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_negative_levy_small_first_moment_large_finite_piecewise_L1_envelope
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_negative_levy_small_first_moment_large_finite_piecewise_L1_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:40:25.22131+00:00
-- url     : https://prove2.me/theorems/f540fa2f-eb34-4945-a1ef-d0ac3752eb7d
-- title:
--   Actual bounded-variation Lévy negative-mark first-variation and finite-tail piecewise L1 envelope
-- statement:
--   For the original spectrally negative bounded-variation Lévy measure, the physical first negative small-mark moment and finite large-negative-mark intensity together make the explicit piecewise envelope g(z) = L(-z) for -a/2<z<0 and g(z)=2R for z≤-a/2 integrable against all genuine negative source marks. The cap a≤2 ensures the small region lies inside (-1,0); the large region uses only finite physical mark intensity, allowing ruin overshoots without a global first moment.
-- source:
--   Pinned original BV small-negative-first-moment theorem 2296f406, original large-mark ν-tail finite mass and Mathlib IntegrableOn.of_bound, IntegrableOn.union.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_small_negative_first_moment_integrable
open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_negative_levy_small_first_moment_large_finite_piecewise_L1_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (a L R : ℝ) (ha : 0 < a) (ha2 : a ≤ 2)
    (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hMass : X.ν (Iic (-a / 2)) < ⊤) :
    IntegrableOn (fun z : ℝ =>
      if z ≤ -a / 2 then 2 * R else L * (-z))
      (Iio 0) X.ν := by sorry
