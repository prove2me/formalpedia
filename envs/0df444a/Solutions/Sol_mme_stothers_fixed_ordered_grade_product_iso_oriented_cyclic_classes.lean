-- Prove2me | solution 1 for mme_stothers_fixed_ordered_grade_product_iso_oriented_cyclic_classes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:36:15.344895+00:00
-- url     : https://prove2.me/submissions/346ad443-d038-441d-a08d-6faf8db83b73

import Mathlib.Tactic
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_oriented_cyclic_classes
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Theorems.Thm_mme_toQ_kronFin
import Theorems.Thm_mme_stothers_cwFourth_cyclic_block_iso

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace MME.StothersFourth.NumericM5

private def orientedCyclicAddress (z : Fin 15 × Fin 3) : Fin 3 → Fin 9 :=
  match z.2.val with
  | 0 => fixedOrientedRep z.1
  | 1 => fixedModeRelabel cyclicPerm (fixedOrientedRep z.1)
  | _ => fixedModeRelabel (cyclicPerm.trans cyclicPerm)
      (fixedOrientedRep z.1)

private theorem orientedCyclicAddress_injective :
    Function.Injective orientedCyclicAddress := by
  decide

private theorem orientedCyclicAddress_range_iff_orbit
    (rho : Fin 3 → Fin 9) :
    (∃ z : Fin 15 × Fin 3, orientedCyclicAddress z = rho) ↔
      ∃ r : Fin 10, fixedSameOrbitExplicit rho (classRep r) := by
  revert rho
  decide

private theorem fixedJointMultiplicity_orientedCyclicAddress
    (m : ℕ) (z : Fin 15 × Fin 3) :
    fixedJointMultiplicity m (orientedCyclicAddress z) =
      fixedProfileCount m (fixedOrientedClass z.1) := by
  rcases z with ⟨t, k⟩
  fin_cases t <;> fin_cases k <;>
    simp [Fin.sum_univ_succ, orientedCyclicAddress, fixedJointMultiplicity,
      fixedSameOrbitExplicit, fixedProfileCount,
      fixedProfileBaseCount, cwFourthBlockType,
      fixedOrientedRep, fixedOrientedClass, fixedModeRelabel,
      cyclicPerm, swapFirstTwoPerm, classRep]

private theorem fixedJointMultiplicity_eq_zero_of_not_mem_oriented_image
    (m : ℕ) (rho : Fin 3 → Fin 9)
    (h : rho ∉ Finset.univ.image orientedCyclicAddress) :
    fixedJointMultiplicity m rho = 0 := by
  have hnrange : ¬ ∃ z : Fin 15 × Fin 3,
      orientedCyclicAddress z = rho := by
    simpa only [Finset.mem_image, Finset.mem_univ, true_and] using h
  have hnorbit : ¬ ∃ r : Fin 10,
      fixedSameOrbitExplicit rho (classRep r) :=
    (not_congr (orientedCyclicAddress_range_iff_orbit rho)).mp hnrange
  simp only [fixedJointMultiplicity]
  apply Finset.sum_eq_zero
  intro r hr
  rw [if_neg]
  intro horbit
  exact hnorbit ⟨r, horbit⟩

private theorem oriented_weighted_product
    {M : Type*} [CommMonoid M]
    (X : (Fin 3 → Fin 9) → M) (m : ℕ) :
    (∏ z : Fin 15 × Fin 3,
      X (orientedCyclicAddress z) ^
        fixedProfileCount m (fixedOrientedClass z.1)) =
      ∏ rho : Fin 3 → Fin 9,
        X rho ^ fixedJointMultiplicity m rho := by
  classical
  apply Finset.prod_of_injOn orientedCyclicAddress
  · exact orientedCyclicAddress_injective.injOn
  · simp
  · intro rho hrho hnimage
    have hnfin : rho ∉ Finset.univ.image orientedCyclicAddress := by
      intro hmem
      rcases Finset.mem_image.mp hmem with ⟨z, hz, hzr⟩
      exact hnimage ⟨z, by simp, hzr⟩
    have hzero := fixedJointMultiplicity_eq_zero_of_not_mem_oriented_image
      m rho hnfin
    rw [hzero, pow_zero]
  · intro z hz
    rw [fixedJointMultiplicity_orientedCyclicAddress]

private theorem permObj_trans_iso
    {K : Type u} [Field K] {d : ℕ}
    (e e' : Equiv.Perm (Fin d)) (X : TensorObj K d) :
    TensorObj.Isomorphic
      (TensorObj.permObj e' (TensorObj.permObj e X))
      (TensorObj.permObj (e.trans e') X) := by
  have ht : (TensorObj.permObj e' (TensorObj.permObj e X)).t =
      (TensorObj.permObj (e.trans e') X).t := by
    exact PiTensorProduct.reindex_reindex e e' X.t
  constructor
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    have hmap := LinearMap.congr_fun
      (PiTensorProduct.map_id
        (R := K) (s := (TensorObj.permObj (e.trans e') X).V))
      (TensorObj.permObj (e.trans e') X).t
    exact hmap.trans ht.symm
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    have hmap := LinearMap.congr_fun
      (PiTensorProduct.map_id
        (R := K) (s := (TensorObj.permObj e' (TensorObj.permObj e X)).V))
      (TensorObj.permObj e' (TensorObj.permObj e X)).t
    exact hmap.trans ht

private theorem fixedModeRelabel_cyclic_twice (rho : Fin 3 → Fin 9) :
    fixedModeRelabel cyclicPerm
        (fixedModeRelabel cyclicPerm rho) =
      fixedModeRelabel (cyclicPerm.trans cyclicPerm) rho := by
  funext i
  fin_cases i <;> rfl

private def cyclicAddressOf (rho : Fin 3 → Fin 9)
    (k : Fin 3) : Fin 3 → Fin 9 :=
  match k.val with
  | 0 => rho
  | 1 => fixedModeRelabel cyclicPerm rho
  | _ => fixedModeRelabel (cyclicPerm.trans cyclicPerm) rho

private theorem cyclic_block_second_rotation_iso
    {K : Type u} [Field K] (q : ℕ) (rho : Fin 3 → Fin 9) :
    TensorObj.Isomorphic
      ((cwFourthCanonicalGrading K q).blockSubtensor
        (fixedModeRelabel (cyclicPerm.trans cyclicPerm) rho))
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
        ((cwFourthCanonicalGrading K q).blockSubtensor rho)) := by
  let B := (cwFourthCanonicalGrading K q).blockSubtensor rho
  have hfirst := mme_stothers_cwFourth_cyclic_block_iso (K := K) q rho
  have hsecond0 := mme_stothers_cwFourth_cyclic_block_iso (K := K) q
    (fixedModeRelabel cyclicPerm rho)
  have hsecond : TensorObj.Isomorphic
      ((cwFourthCanonicalGrading K q).blockSubtensor
        (fixedModeRelabel (cyclicPerm.trans cyclicPerm) rho))
      (TensorObj.permObj cyclicPerm
        ((cwFourthCanonicalGrading K q).blockSubtensor
          (fixedModeRelabel cyclicPerm rho))) := by
    simpa only [fixedModeRelabel_cyclic_twice] using hsecond0
  exact hsecond.trans
    ((TensorObj.permObj_isomorphic cyclicPerm hfirst).trans
      (permObj_trans_iso cyclicPerm cyclicPerm B))

private theorem cyclic_block_toQ_product
    {K : Type u} [Field K] (q : ℕ) (rho : Fin 3 → Fin 9) :
    TensorQ.toQ
        (cyclicSymmetrization
          ((cwFourthCanonicalGrading K q).blockSubtensor rho)) =
      ∏ k : Fin 3,
        TensorQ.toQ
          ((cwFourthCanonicalGrading K q).blockSubtensor
            (cyclicAddressOf rho k)) := by
  have hfirstQ :
      TensorQ.toQ
          (TensorObj.permObj cyclicPerm
            ((cwFourthCanonicalGrading K q).blockSubtensor rho)) =
        TensorQ.toQ
          ((cwFourthCanonicalGrading K q).blockSubtensor
            (fixedModeRelabel cyclicPerm rho)) :=
    ((TensorQ.toQ_eq_iff).2
      (mme_stothers_cwFourth_cyclic_block_iso (K := K) q rho)).symm
  have hsecondQ :
      TensorQ.toQ
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            ((cwFourthCanonicalGrading K q).blockSubtensor rho)) =
        TensorQ.toQ
          ((cwFourthCanonicalGrading K q).blockSubtensor
            (fixedModeRelabel (cyclicPerm.trans cyclicPerm) rho)) :=
    ((TensorQ.toQ_eq_iff).2
      (cyclic_block_second_rotation_iso (K := K) q rho)).symm
  rw [cyclicSymmetrization_eq_public_perm,
    TensorQ.toQ_kron, TensorQ.toQ_kron, hfirstQ, hsecondQ]
  simp [cyclicAddressOf, Fin.prod_univ_succ]

private theorem orientedCyclicAddress_eq
    (t : Fin 15) (k : Fin 3) :
    orientedCyclicAddress (t, k) =
      cyclicAddressOf (fixedOrientedRep t) k := by
  fin_cases k <;> rfl

private theorem orientedCyclicAddress_eq_pair (z : Fin 15 × Fin 3) :
    orientedCyclicAddress z =
      cyclicAddressOf (fixedOrientedRep z.1) z.2 :=
  orientedCyclicAddress_eq z.1 z.2

theorem oriented_regrouping_iso
    {K : Type u} [Field K] (m : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.kronFin 15 (fun t ↦
        (cyclicSymmetrization
          ((cwFourthCanonicalGrading K 6).blockSubtensor
            (fixedOrientedRep t))).kronPow
              (fixedProfileCount m (fixedOrientedClass t))))
      (let e : (Fin 3 → Fin 9) ≃ Fin 729 := by
          classical
          exact (Fintype.equivFin (Fin 3 → Fin 9)).trans (finCongr (by simp))
        TensorObj.kronFin 729 (fun s ↦
          ((cwFourthCanonicalGrading K 6).blockSubtensor
            (e.symm s)).kronPow
              (fixedJointMultiplicity m (e.symm s)))) := by
  classical
  let e : (Fin 3 → Fin 9) ≃ Fin 729 := by
    classical
    exact (Fintype.equivFin (Fin 3 → Fin 9)).trans (finCongr (by simp))
  change TensorObj.Isomorphic
      (TensorObj.kronFin 15 (fun t ↦
        (cyclicSymmetrization
          ((cwFourthCanonicalGrading K 6).blockSubtensor
            (fixedOrientedRep t))).kronPow
              (fixedProfileCount m (fixedOrientedClass t))))
      (TensorObj.kronFin 729 (fun s ↦
        ((cwFourthCanonicalGrading K 6).blockSubtensor
          (e.symm s)).kronPow
            (fixedJointMultiplicity m (e.symm s))))
  apply (TensorQ.toQ_eq_iff).1
  rw [mme_toQ_kronFin, mme_toQ_kronFin]
  simp_rw [TensorQ.toQ_kronPow, cyclic_block_toQ_product]
  have hpow : ∀ t : Fin 15,
      (∏ k : Fin 3,
          TensorQ.toQ
            ((cwFourthCanonicalGrading K 6).blockSubtensor
              (cyclicAddressOf (fixedOrientedRep t) k))) ^
          fixedProfileCount m (fixedOrientedClass t) =
        ∏ k : Fin 3,
          (TensorQ.toQ
            ((cwFourthCanonicalGrading K 6).blockSubtensor
              (cyclicAddressOf (fixedOrientedRep t) k))) ^
            fixedProfileCount m (fixedOrientedClass t) := by
    intro t
    exact (Finset.prod_pow Finset.univ
      (fixedProfileCount m (fixedOrientedClass t))
      (fun k : Fin 3 ↦ TensorQ.toQ
        ((cwFourthCanonicalGrading K 6).blockSubtensor
          (cyclicAddressOf (fixedOrientedRep t) k)))).symm
  simp_rw [hpow]
  rw [← Fintype.prod_prod_type']
  have hleft :
      (∏ z : Fin 15 × Fin 3,
        (TensorQ.toQ
          ((cwFourthCanonicalGrading K 6).blockSubtensor
            (cyclicAddressOf (fixedOrientedRep z.1) z.2))) ^
          fixedProfileCount m (fixedOrientedClass z.1)) =
        ∏ rho : Fin 3 → Fin 9,
          (TensorQ.toQ
            ((cwFourthCanonicalGrading K 6).blockSubtensor rho)) ^
            fixedJointMultiplicity m rho := by
    simpa only [orientedCyclicAddress_eq_pair] using
      oriented_weighted_product
        (fun rho ↦ TensorQ.toQ
          ((cwFourthCanonicalGrading K 6).blockSubtensor rho)) m
  rw [hleft]
  let X : (Fin 3 → Fin 9) → TensorQ K 3 := fun rho ↦
    (TensorQ.toQ
      ((cwFourthCanonicalGrading K 6).blockSubtensor rho)) ^
        fixedJointMultiplicity m rho
  change (∏ rho : Fin 3 → Fin 9, X rho) =
    ∏ s : Fin 729, X (e.symm s)
  calc
    (∏ rho : Fin 3 → Fin 9, X rho) =
        ∏ rho : Fin 3 → Fin 9, X (e.symm (e rho)) := by
          congr 1
          funext rho
          rw [Equiv.symm_apply_apply]
    _ = ∏ s : Fin 729, X (e.symm s) :=
      Equiv.prod_comp e (fun s : Fin 729 ↦ X (e.symm s))

end MME.StothersFourth.NumericM5

theorem solution
    {K : Type u} [Field K] (m : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.kronFin 15 (fun t ↦
        (cyclicSymmetrization
          ((MME.StothersFourth.cwFourthCanonicalGrading K 6).blockSubtensor
            (MME.StothersFourth.fixedOrientedRep t))).kronPow
              (MME.StothersFourth.fixedProfileCount m
                (MME.StothersFourth.fixedOrientedClass t))))
      (let e : (Fin 3 → Fin 9) ≃ Fin 729 := by
          classical
          exact (Fintype.equivFin (Fin 3 → Fin 9)).trans (finCongr (by simp))
        TensorObj.kronFin 729 (fun s ↦
          ((MME.StothersFourth.cwFourthCanonicalGrading K 6).blockSubtensor
            (e.symm s)).kronPow
              (MME.StothersFourth.fixedJointMultiplicity m (e.symm s)))) := by
  exact MME.StothersFourth.NumericM5.oriented_regrouping_iso m
