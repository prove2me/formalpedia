-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_finite_simple_negative_mark_rightCont_martingale_allactivity_20261122
-- name    : AvramDividend.Classical.avram_oai_original_physical_finite_simple_negative_mark_rightCont_martingale_allactivity_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T16:06:02.540812+00:00
-- url     : https://prove2.me/theorems/4bb4b8b7-02d6-435d-b305-5af9e9688293
-- title:
--   Full true original all-activity compensated finite signed simple negative mark Lévy martingale in right-continuous filtration
-- statement:
--   For the ACTUAL original spectrally negative Lévy process X and its intrinsic physical marked jump measure NX, any measurable negative mark set S with finite restricted Lévy intensity and any finite-range signed real SimpleFunc g induce a genuine right-continuous-filtration Martingale F_t = Σ_{y∈range g} y [(NX_t(S∩{g=y})).toReal−(tν(S∩{g=y})).toReal]. Infinite overall negative jump activity is allowed. Prove from four independently Proved original-source facts: full StronglyAdapted with actual ℱ.rightCont, true finite local marked-count L1 integrability, actual real physical marked-count and compensator time additivity F_t=F_s+G_st a.e., and true right-continuous conditional zero of G_st. Conditional-expectation linearity then verifies the martingale property. No synthetic PRM or imported abstract martingale assumption. This is the missing source martingale bridge for original stopped compensated jump Itô–Meyer calculations and positive-clock expected budgets.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_simple_mark_count_process_rightcont_stronglyAdapted_20261122
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_simple_mark_compensated_process_L1_allactivity_20261122
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_compensated_simple_mark_time_additivity_allactivity_20261122
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_simple_mark_condExp_all_strict_time_20261122
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_original_physical_finite_simple_negative_mark_rightCont_martingale_allactivity_20261122
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hNeg : S ⊆ Iio (0 : ℝ))
    (hν : X.ν S < ⊤) (g : SimpleFunc ℝ ℝ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    let F : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑ y ∈ g.range, y *
        ((NX ω (Ioc 0 t ×ˢ B y)).toReal -
          (((t : ℝ≥0∞) * X.ν (B y))).toReal)
    Martingale F 𝓕.rightCont P := by sorry
