-- Prove2me | solution 1 for folding_preserves_agreement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:34:49.226367+00:00
-- url     : https://prove2.me/submissions/1d151453-492f-44fe-85b9-4214520c3032

import Definitions.Def_SimpleRbrFri_State
import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Theorems.Thm_folding_event_implies_bad_event

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]
    (D : Finset F) (m : ℕ) (d : ℕ)
    (hm : m > 0) (hd : d ≥ m)
    (h_foldable : IsFoldable D m)
    (bound : ℝ) (errorstar : ℕ → ℝ → ℝ)
    (h_mca : MutualCorrelatedAgreement powersGenerator
      (reedSolomon (pow_domain D m) (d / m)) bound errorstar)
    (f : F → F) (delta : ℝ)
    (h_delta_nonneg : 0 ≤ delta) (h_delta_lt : delta < 1 - bound) :
    (PMF.uniformOfFintype F).toMeasure
      {r | FoldingBadEvent D m (reedSolomon D d)
        (reedSolomon (pow_domain D m) (d / m)) f delta r} ≤
      ENNReal.ofReal (errorstar m delta) := by
      have h_folding_event_subset :
          {r : F | FoldingBadEvent D m (reedSolomon D d)
            (reedSolomon (pow_domain D m) (d / m)) f delta r} ⊆
          {r : F | BadEvent (reedSolomon (pow_domain D m) (d / m)) m
            (folding_components D m f) delta (fun i ↦ r ^ (i : ℕ))} := by
        exact fun r hr ↦ by simpa using folding_event_implies_bad_event D m d hm hd f delta r hr
      refine (MeasureTheory.measure_mono h_folding_event_subset).trans ?_
      refine le_trans (le_of_eq ?_) (h_mca m (folding_components D m f) delta h_delta_nonneg h_delta_lt)
      rw [show (powersGenerator m) = (PMF.uniformOfFintype F).map
        (fun r ↦ fun i : Fin m ↦ r ^ (i : ℕ)) from rfl]
      simp only [PMF.toMeasure_apply_fintype, Set.indicator, Set.mem_setOf_eq,
        PMF.uniformOfFintype_apply, PMF.map_apply]
      rw [← Finset.sum_subset <|
        Finset.subset_univ <|
          Finset.image (fun x ↦ fun i : Fin m ↦ x ^ (i : ℕ)) Finset.univ]
      · rw [Finset.sum_image']
        intro i hi
        split_ifs with h_bad
        · simp_all only [Finset.sum_ite]
          rw [tsum_eq_sum]
          any_goals exact Finset.univ.filter fun j ↦
            (fun i_1 : Fin m ↦ j ^ (i_1 : ℕ)) = fun i_1 : Fin m ↦ i ^ (i_1 : ℕ)
          · simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_zero, add_zero]
            congr! 2
            congr! 1
            grind
          · grind
        · simp_all [Finset.sum_ite]
      · intro x _ hx
        split_ifs with h
        · simp_all only [gt_iff_lt, ge_iff_le, Set.setOf_subset_setOf, Finset.mem_univ,
            Finset.mem_image, funext_iff, true_and, not_exists, not_forall, ENNReal.tsum_eq_zero,
            ite_eq_right_iff, ENNReal.inv_eq_zero, ENNReal.natCast_ne_top, imp_false]
          exact fun i ↦ by obtain ⟨j, hj⟩ := hx i; exact ⟨j, Ne.symm hj⟩
        · simp_all only [gt_iff_lt, ge_iff_le, Set.setOf_subset_setOf, Finset.mem_univ,
            Finset.mem_image, funext_iff, true_and, not_exists, not_forall]
