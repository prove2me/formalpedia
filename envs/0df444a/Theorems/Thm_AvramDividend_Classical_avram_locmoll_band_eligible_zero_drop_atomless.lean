-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_eligible_zero_drop_atomless
-- name    : AvramDividend.Classical.avram_locmoll_band_eligible_zero_drop_atomless
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-27T00:19:07.870213+00:00
-- url     : https://prove2.me/theorems/c50c712f-5aa9-5ca7-8f58-bf4a989e801d
-- title:
--   The eligible Stieltjes measure restricted to zero right payments is atomless
-- statement:
--   The eligible Stieltjes measure restricted to zero right payments is atomless
-- source:
--   Exact atomic diffuse secant integral b980c2dc-b50f-4bb4-b148-7f7a2859258e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_eligible_zero_drop_atomless
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (H : ℝ≥0) :
    let S : Set ℝ := paymentTimes (ruinTime X x D ω) ∩ Iic (H : ℝ)
    let U : Set ℝ := {t : ℝ | rightLimit D t.toNNReal ω = D t.toNNReal ω}
    let μ := (dividendMeasure D ω).restrict S
    NullSingletonClass (μ.restrict U) := by sorry
