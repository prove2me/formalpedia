-- Prove2me | solution 1 for mme_dwz_kronFin_hole_cover_tensor_repair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T12:11:48.354044+00:00
-- url     : https://prove2.me/submissions/d88ddb2e-cddf-45c9-b492-2f6e11582e0c

import Theorems.Thm_mme_dwz_hole_cover_exact_once_tensor_repair_poly
import Theorems.Thm_mme_dwz_table2_useful_block_shuffle_system
import Theorems.Thm_mme_dwz_table2_exact_outer_profile_usefulBlock_nonempty
import Theorems.Thm_mme_dwz_kronFin_labelled_broken_family_realizeOwned

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZSquare MME.DWZTable2StandardForm
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

private def groupedPositionFiberEquivForRepair (m : ℕ) (s : Fin 15) :
    Fin (MME.DWZTable2Counts.component s * m) ≃
      {p : GroupedPosition m // groupedOuter p = s} where
  toFun r := ⟨⟨s, r⟩, rfl⟩
  invFun p := by
    rcases p with ⟨⟨s', r⟩, hs⟩
    dsimp only [groupedOuter] at hs
    subst s'
    exact r
  left_inv r := rfl
  right_inv p := by
    rcases p with ⟨⟨s', r⟩, hs⟩
    dsimp only [groupedOuter] at hs
    subst s'
    rfl

theorem solution
    (K : Type u) [Field K] (m N ell : ℕ) {s : ℕ}
    (hN : 0 < N) (hell : 0 < ell)
    (copies : Fin s → BrokenBlockCopy (DWZStandardBlock m))
    (hcard : Fintype.card (DWZStandardBlock m) ≤ 2 ^ (N * ell))
    (hsum : ((N * ell + 1 : ℕ) : ℝ) ≤
      ∑ t : Fin s, nonholeFraction (copies t)) :
    let D : DWZStandardLabelledData K m :=
      { X := TensorObj.kronFin 15
          (fun r : Fin 15 ↦ restrictedComponentPower K r m)
        basis := TensorObj.kronFinModePiBasis 15
          (fun r : Fin 15 ↦ restrictedComponentPower K r m) 2
          (fun r ↦ restrictedComponentZBasis K r m)
        label := groupedUsefulBlock m }
    let G : Fin s → D.X.TypeGrading 2 := fun t ↦
      D.X.basisZAllowedGrading D.basis
        (fun W ↦ D.label W ∈ (copies t).nonholes)
    TensorObj.Restrict
      ({ V := D.X.V
         t := ∑ block : DWZStandardBlock m,
           dwzLabelledUsefulBlockTensor K m D block } : TensorObj K 3)
      (TensorObj.bigAdd
        (fun t ↦ (G t).blockSubtensor (fun _ ↦ 0))) := by
  classical
  dsimp only
  let D : DWZStandardLabelledData K m :=
    { X := TensorObj.kronFin 15
        (fun r : Fin 15 ↦ restrictedComponentPower K r m)
      basis := TensorObj.kronFinModePiBasis 15
        (fun r : Fin 15 ↦ restrictedComponentPower K r m) 2
        (fun r ↦ restrictedComponentZBasis K r m)
      label := groupedUsefulBlock m }
  let G : Fin s → D.X.TypeGrading 2 := fun t ↦
    D.X.basisZAllowedGrading D.basis
      (fun W ↦ D.label W ∈ (copies t).nonholes)
  change TensorObj.Restrict
    ({ V := D.X.V
       t := ∑ block : DWZStandardBlock m,
         dwzLabelledUsefulBlockTensor K m D block } : TensorObj K 3)
    (TensorObj.bigAdd
      (fun t ↦ (G t).blockSubtensor (fun _ ↦ 0)))
  have hProfile : ∀ r : Fin 15,
      Fintype.card {p : GroupedPosition m // groupedOuter p = r} =
        MME.DWZTable2Counts.component r * m := by
    intro r
    simpa using Fintype.card_congr
      (groupedPositionFiberEquivForRepair m r).symm
  let : Nonempty (DWZStandardBlock m) :=
    mme_dwz_table2_exact_outer_profile_usefulBlock_nonempty
      m (groupedOuter (m := m)) hProfile
  obtain ⟨system, hsystem⟩ :=
    mme_dwz_table2_useful_block_shuffle_system
      m (groupedOuter (m := m))
  have hmove : ∀ g, system.move g = MulAction.toPerm g := by
    intro g
    ext block
    exact hsystem g block
  obtain ⟨shuffleMap, hrealize⟩ :=
    mme_dwz_kronFin_labelled_broken_family_realizeOwned K m copies
  have realizeOwned :
      ∀ (shuffles : Fin s → UsefulBlockShuffleGroup
            (groupedOuter (m := m)))
          (owner : DWZStandardBlock m → Fin s),
        (∀ block : DWZStandardBlock m,
          (system.move (shuffles (owner block))).symm block ∈
            (copies (owner block)).nonholes) →
        ∃ f : ∀ t i,
            ((G t).blockSubtensor (fun _ ↦ 0)).V i →ₗ[K] D.X.V i,
          (∀ t, f t 0 = shuffleMap shuffles t 0) ∧
          (∀ t, f t 1 = shuffleMap shuffles t 1) ∧
          ∀ t,
            PiTensorProduct.map (f t)
                ((G t).blockSubtensor (fun _ ↦ 0)).t =
              ∑ block : DWZStandardBlock m,
                if t = owner block then
                  dwzLabelledUsefulBlockTensor K m D block
                else 0 := by
    intro shuffles owner howner
    apply hrealize shuffles owner
    intro block
    simpa only [← hmove (shuffles (owner block))] using howner block
  obtain ⟨_, _, _, _, _, _, _, _, hrestrict⟩ :=
    mme_dwz_hole_cover_exact_once_tensor_repair_poly
      system N ell hN hell copies hcard hsum
      (fun t ↦ (G t).blockSubtensor (fun _ ↦ 0))
      (fun block ↦ dwzLabelledUsefulBlockTensor K m D block)
      shuffleMap realizeOwned
  exact hrestrict
