-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_generic_indep_same_count_law_prefix_sum
-- name    : AvramDividend.Classical.avram_a06_generic_indep_same_count_law_prefix_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:40:18.544519+00:00
-- url     : https://prove2.me/theorems/3af59764-9e08-491c-84f7-6427086bf547
-- title:
--   Independent counts of identical law yield identically distributed mark prefix sums
-- statement:
--   Two almost-everywhere-measurable integer-valued counts with the same law, each independent of a common full mark stream, yield identically distributed sums over their respective random prefixes.
-- source:
--   Factor the joint distribution of count and marks into product measures using IndepFun.map_prod_eq_prod_map_map; use equality of count marginals and push forward along measurable finite prefix sum.

import Mathlib
open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_generic_indep_same_count_law_prefix_sum
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (N N' : Ω → ℕ) (M : Ω → ℕ → ℝ)
    (hN : AEMeasurable N P) (hN' : AEMeasurable N' P)
    (hM : AEMeasurable M P)
    (hInd : IndepFun N M P) (hInd' : IndepFun N' M P)
    (hLaw : IdentDistrib N N' P P) :
    IdentDistrib
      (fun ω => ∑ j ∈ Finset.range (N ω), M ω j)
      (fun ω => ∑ j ∈ Finset.range (N' ω), M ω j) P P := by sorry
