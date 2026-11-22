-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_simple_mark_count_process_rightcont_stronglyAdapted_20261122
-- name    : AvramDividend.Classical.avram_oai_original_physical_simple_mark_count_process_rightcont_stronglyAdapted_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:42:02.138367+00:00
-- url     : https://prove2.me/theorems/c522b292-b47c-4213-be3f-951132a8a6af
-- title:
--   Actual intrinsic marked finite simple Lévy count process is strongly adapted to the original right-continuous filtration, all activities
-- statement:
--   For the original intrinsic sample-path Lévy marked jump measure NX, an arbitrary measurable marked region S and arbitrary real finite-range SimpleFunc g, form the finite sum F_t=Σ_{y∈range g} y (NX((0,t]×(S∩{g=y}))−tν(S∩{g=y})). This process is StronglyAdapted to the original right-continuous filtration, for all times and without global finite jump activity or integrability assumptions on ν(S). The proof uses already Proved original earlier-marked-cell pathwise count StronglyMeasurable[ℱ.rightCont t] source lemma 6189fbe3 for each Borel simple fibre, then Mathlib Finset.stronglyMeasurable_sum. Together with the newly Proved actual physical conditional signed simple-mark increment zero theorem, this supplies the two genuinely source-based stochastic prerequisites for constructing real finite-simple marked Lévy martingales.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_actual_earlier_negative_marked_cell_count_later_filtration_stronglyMeasurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_original_physical_simple_mark_count_process_rightcont_stronglyAdapted_20261122
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Set ℝ) (hS : MeasurableSet S)
    (g : SimpleFunc ℝ ℝ) :
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
    StronglyAdapted 𝓕.rightCont F := by sorry
