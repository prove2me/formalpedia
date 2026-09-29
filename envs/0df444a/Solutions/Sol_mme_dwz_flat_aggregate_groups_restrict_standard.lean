-- Prove2me | solution 1 for mme_dwz_flat_aggregate_groups_restrict_standard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T19:41:03.659725+00:00
-- url     : https://prove2.me/submissions/f776e3dc-a0e4-4f9a-a0e3-9ed0b21ffc0e

import Theorems.Thm_mme_bigAdd_list_flatten_isomorphic_nested
import Theorems.Thm_mme_bigAdd_list_prefix_restrict
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_dwz_kronFin_hole_cover_restrict_standard
import Theorems.Thm_mme_dwz_table2_exact_outer_profile_usefulBlock_nonempty

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZSquare MME.DWZTable2StandardForm
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

private def groupedPositionFiberEquivForVariableAggregate (m : ℕ) (s : Fin 15) :
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

/-- Variable-size aggregate Hole groups forming a literal prefix of a flat
broken-copy family repair one complete standard tensor per group. -/
theorem solution
    (K : Type u) [Field K] (m N ell : ℕ)
    (hN : 0 < N) (hell : 0 < ell)
    (groups : List (List (BrokenBlockCopy (DWZStandardBlock m))))
    (remainder : List (BrokenBlockCopy (DWZStandardBlock m)))
    (hcard : Fintype.card (DWZStandardBlock m) ≤ 2 ^ (N * ell))
    (haggregate : ∀ group ∈ groups,
      ((N * ell + 1 : ℕ) : ℝ) ≤
        (group.map nonholeFraction).sum) :
    let D : DWZStandardLabelledData K m :=
      { X := TensorObj.kronFin 15
          (fun r : Fin 15 ↦ restrictedComponentPower K r m)
        basis := TensorObj.kronFinModePiBasis 15
          (fun r : Fin 15 ↦ restrictedComponentPower K r m) 2
          (fun r ↦ restrictedComponentZBasis K r m)
        label := groupedUsefulBlock m }
    let G : BrokenBlockCopy (DWZStandardBlock m) → D.X.TypeGrading 2 :=
      fun copy ↦ D.X.basisZAllowedGrading D.basis
        (fun W ↦ D.label W ∈ copy.nonholes)
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin groups.length ↦ D.X))
      (TensorObj.bigAdd (fun r : Fin (groups.flatten ++ remainder).length ↦
        (G ((groups.flatten ++ remainder).get r)).blockSubtensor
          (fun _ ↦ 0))) := by
  classical
  dsimp only
  let D : DWZStandardLabelledData K m :=
    { X := TensorObj.kronFin 15
        (fun r : Fin 15 ↦ restrictedComponentPower K r m)
      basis := TensorObj.kronFinModePiBasis 15
        (fun r : Fin 15 ↦ restrictedComponentPower K r m) 2
        (fun r ↦ restrictedComponentZBasis K r m)
      label := groupedUsefulBlock m }
  let G : BrokenBlockCopy (DWZStandardBlock m) → D.X.TypeGrading 2 :=
    fun copy ↦ D.X.basisZAllowedGrading D.basis
      (fun W ↦ D.label W ∈ copy.nonholes)
  let X : BrokenBlockCopy (DWZStandardBlock m) → TensorObj K 3 :=
    fun copy ↦ (G copy).blockSubtensor (fun _ ↦ 0)
  have hProfile : ∀ r : Fin 15,
      Fintype.card {p : GroupedPosition m // groupedOuter p = r} =
        MME.DWZTable2Counts.component r * m := by
    intro r
    simpa using Fintype.card_congr
      (groupedPositionFiberEquivForVariableAggregate m r).symm
  let : Nonempty (DWZStandardBlock m) :=
    mme_dwz_table2_exact_outer_profile_usefulBlock_nonempty
      m (groupedOuter (m := m)) hProfile
  have hgroup : ∀ a : Fin groups.length,
      TensorObj.Restrict D.X
        (TensorObj.bigAdd (fun b : Fin (groups.get a).length ↦
          X ((groups.get a).get b))) := by
    intro a
    apply mme_dwz_kronFin_hole_cover_restrict_standard
      K m N ell hN hell
      (fun b : Fin (groups.get a).length ↦ (groups.get a).get b)
      hcard
    have ha : groups.get a ∈ groups := List.get_mem groups a
    rw [← List.sum_ofFn]
    have hfn :
        List.ofFn (fun t : Fin (groups.get a).length ↦
          nonholeFraction ((groups.get a).get t)) =
            (groups.get a).map nonholeFraction := by
      change List.ofFn (nonholeFraction ∘ (groups.get a).get) = _
      rw [← List.map_ofFn, List.ofFn_get]
    rw [hfn]
    exact haggregate (groups.get a) ha
  have hnested : TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin groups.length ↦ D.X))
      (TensorObj.bigAdd (fun a : Fin groups.length ↦
        TensorObj.bigAdd (fun b : Fin (groups.get a).length ↦
          X ((groups.get a).get b)))) :=
    mme_bigAdd_mono_restrict hgroup
  have hflatten : TensorObj.Restrict
      (TensorObj.bigAdd (fun a : Fin groups.length ↦
        TensorObj.bigAdd (fun b : Fin (groups.get a).length ↦
          X ((groups.get a).get b))))
      (TensorObj.bigAdd (fun r : Fin groups.flatten.length ↦
        X (groups.flatten.get r))) :=
    (mme_bigAdd_list_flatten_isomorphic_nested groups X).2
  have hprefix : TensorObj.Restrict
      (TensorObj.bigAdd (fun r : Fin groups.flatten.length ↦
        X (groups.flatten.get r)))
      (TensorObj.bigAdd
        (fun r : Fin (groups.flatten ++ remainder).length ↦
          X ((groups.flatten ++ remainder).get r))) :=
    mme_bigAdd_list_prefix_restrict (K := K) (d := 3)
      (by norm_num) X groups.flatten remainder
  exact TensorObj.Restrict.trans (TensorObj.Restrict.trans hnested hflatten)
    (by simpa only [X, G, D] using hprefix)
