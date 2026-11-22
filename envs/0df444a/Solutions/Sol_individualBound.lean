-- Prove2me | solution 1 for individualBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:42:47.185003+00:00
-- url     : https://prove2.me/submissions/2e646e20-0c9b-43b4-90dd-ba49a7c1db89

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_LocalLemma
import Theorems.Thm_iteration

set_option autoImplicit true
open MeasureTheory ProbabilityTheory Measure
variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {A : ι → Set Ω} {N : ι → Finset ι} {x : ι → ℝ} {i j : ι} {S T : Finset ι}
open Finset
theorem _root_.solution [IsProbabilityMeasure P] (hA : ∀ i, MeasurableSet (A i))
    (hN : lopsidedCondition P A N)
    (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i ≤ 1)
    (hAx : ∀ i, P.real (A i) ≤ x i * ∏ j ∈ N i, (1 - x j))
    (hiS : i ∉ S) :
    IndividualBound P A x i S := by
  classical
  induction S using strongInduction generalizing i with
  | H S ih =>
    let S₁ : Finset ι := S ∩ N i
    let S₂ : Finset ι := S \ S₁
    have hS : S₁ ∪ S₂ = S := by simp [S₁, S₂, union_comm (S ∩ N i), sdiff_union_inter]
    rw [IndividualBound]
    calc
      P.real (A i ∩ ⋂ j ∈ S, (A j)ᶜ) ≤ P.real (A i ∩ ⋂ j ∈ S₂, (A j)ᶜ) := by
        rw [← hS, Finset.set_biInter_inter]
        refine measureReal_mono ?_
        gcongr
        exact Set.inter_subset_right
      _ ≤ P.real (A i) * P.real (⋂ j ∈ S₂, (A j)ᶜ) :=
        hN.real (by simp [S₂, hiS]) (by simp [S₂, S₁, disjoint_sdiff])
      _ ≤ x i * (∏ j ∈ N i, (1 - x j)) * P.real (⋂ j ∈ S₂, (A j)ᶜ) := by gcongr; exact hAx i
      _ = x i * ((∏ j ∈ N i, (1 - x j)) * P.real (⋂ j ∈ S₂, (A j)ᶜ)) := by ring
      _ ≤ x i * ((∏ j ∈ S₁, (1 - x j)) * P.real (⋂ j ∈ S₂, (A j)ᶜ)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ ?_) (hx₀ i)
        · exact prod_le_prod_of_subset_of_le_one (by simp [S₁]) (by simp [hx₁]) (by simp [hx₀])
        · positivity
      _ ≤ x i * P.real (⋂ j ∈ S, (A j)ᶜ) := by
        gcongr
        · exact hx₀ i
        rw [← hS]
        exact iteration hA disjoint_sdiff hx₁ _ (by simp [S₁]) (by simp [S₂]) ih
