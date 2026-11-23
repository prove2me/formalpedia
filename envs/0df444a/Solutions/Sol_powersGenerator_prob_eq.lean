-- Prove2me | solution 1 for powersGenerator_prob_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:42:25.255662+00:00
-- url     : https://prove2.me/submissions/b2db544c-c26e-4556-a24e-33bc4cb2f0b7

import Definitions.Def_SimpleRbrFri_State
import Definitions.Def_SimpleRbrFri_FoldingSoundness

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
open scoped Classical
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    [MeasurableSpace F] [DiscreteMeasurableSpace F] (m : ℕ) (S : Set (Fin m → F)) :
    (@powersGenerator F _ _ (by infer_instance) _ m).toMeasure S =
    (Finset.univ.filter (fun r ↦ (fun i : Fin m ↦ r ^ (i : ℕ)) ∈ S)).card /
      Fintype.card F := by
  -- The measure of S under the powersGenerator is the sum of the measures of the
  -- individual points in S.
  have h_measure : ((powersGenerator m).toMeasure S) =
      ∑ r ∈ Finset.filter (fun r ↦ (fun i : Fin m ↦ r ^ (i : ℕ)) ∈ S)
        Finset.univ, (1 / (Fintype.card F : ENNReal)) := by
    have h_inner : ((powersGenerator m).toMeasure S) = ∑ r ∈ Finset.univ,
        (if (fun i : Fin m ↦ r ^ (i : ℕ)) ∈ S
          then (1 / (Fintype.card F : ENNReal)) else 0) := by
      rw [PMF.toMeasure_apply]
      · simp only [powersGenerator]
        rw [tsum_eq_sum]
        any_goals
          exact Finset.image (fun r ↦ fun i : Fin m ↦ r ^ (i : ℕ)) Finset.univ
        · rw [Finset.sum_image']
          intro r hr
          by_cases hr' : (fun i : Fin m ↦ r ^ (i : ℕ)) ∈ S
          · simp only [hr', Set.indicator_of_mem, PMF.map_apply,
              PMF.uniformOfFintype_apply, one_div]
            rw [tsum_eq_sum]
            congr! 1
            · grind
            · grind
          · simp only [hr', not_false_eq_true, Set.indicator_of_notMem, one_div]
            rw [Finset.sum_eq_zero]
            grind
        · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists,
            Set.indicator_apply_eq_zero, PMF.map_apply, PMF.uniformOfFintype_apply,
            ENNReal.tsum_eq_zero, ite_eq_right_iff, ENNReal.inv_eq_zero,
            ENNReal.natCast_ne_top, imp_false]
          exact fun b hb₁ hb₂ i hi ↦ hb₁ i hi.symm
      · exact DiscreteMeasurableSpace.forall_measurableSet S
    rw [h_inner, Finset.sum_filter]
  simp_all [div_eq_mul_inv]
