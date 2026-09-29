-- Prove2me | solution 1 for mme_dwz_table2_grouped_kronFin_shuffle_automorphism
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T10:34:29.352472+00:00
-- url     : https://prove2.me/submissions/4a2417b0-90a9-4eb0-85bd-05b278488328

import Theorems.Thm_mme_dwz_restricted_component_position_automorphism
import Theorems.Thm_mme_kronFin_modewise_basis_automorphisms_preserve_tensor
import Definitions.Def_mme_dwz_broken_standard_obj
import Definitions.Def_mme_dwz_table2_useful_block_shuffle_action
import Definitions.Def_mme_dwz_restricted_component_z_basis
import Definitions.Def_mme_kronFin_mode_pi_basis
import Definitions.Def_mme_basis_index_permutation

open MME MME.TensorObj MME.DWZComponentRestriction PiTensorProduct Module

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

private def solutionGroupedPositionFiberEquiv (m : ℕ) (s : Fin 15) :
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

private def solutionGroupedShuffleFiberEquiv
    (m : ℕ)
    (g : MME.DWZTable2StandardForm.UsefulBlockShuffleGroup
      (groupedOuter (m := m)))
    (s : Fin 15) :
    {p : GroupedPosition m // groupedOuter p = s} ≃
      {p : GroupedPosition m // groupedOuter p = s} :=
  Equiv.subtypeEquiv g.1 (fun p ↦ by
    constructor
    · intro hp
      rw [g.2 p]
      exact hp
    · intro hgp
      rw [g.2 p] at hgp
      exact hgp)

private def solutionGroupedComponentPerm
    (m : ℕ)
    (g : MME.DWZTable2StandardForm.UsefulBlockShuffleGroup
      (groupedOuter (m := m)))
    (s : Fin 15) :
    Equiv.Perm (Fin (MME.DWZTable2Counts.component s * m)) :=
  (solutionGroupedPositionFiberEquiv m s).trans
    ((solutionGroupedShuffleFiberEquiv m g s).trans
      (solutionGroupedPositionFiberEquiv m s).symm)

private theorem solutionGroupedComponentPerm_spec
    (m : ℕ)
    (g : MME.DWZTable2StandardForm.UsefulBlockShuffleGroup
      (groupedOuter (m := m)))
    (s : Fin 15)
    (r : Fin (MME.DWZTable2Counts.component s * m)) :
    g.1 ⟨s, r⟩ = ⟨s, solutionGroupedComponentPerm m g s r⟩ := by
  have hsub :
      (solutionGroupedShuffleFiberEquiv m g s)
          ((solutionGroupedPositionFiberEquiv m s) r) =
        (solutionGroupedPositionFiberEquiv m s)
          (solutionGroupedComponentPerm m g s r) := by
    change _ = (solutionGroupedPositionFiberEquiv m s)
      ((solutionGroupedPositionFiberEquiv m s).symm
        ((solutionGroupedShuffleFiberEquiv m g s)
          ((solutionGroupedPositionFiberEquiv m s) r)))
    exact ((solutionGroupedPositionFiberEquiv m s).apply_symm_apply _).symm
  exact congrArg Subtype.val hsub

private def solutionGroupedShuffleAllowedWords
    (m : ℕ)
    (g : MME.DWZTable2StandardForm.UsefulBlockShuffleGroup
      (groupedOuter (m := m)))
    (W : GroupedAllowedWords.{u} m) : GroupedAllowedWords.{u} m :=
  fun s ↦
    ⟨PowIndex.reindex (solutionGroupedComponentPerm m g⁻¹ s) (W s).1,
      (mme_dwz_component_word_allowed_reindex_iff
        s m (solutionGroupedComponentPerm m g⁻¹ s) (W s).1).2 (W s).2⟩

private theorem solutionGroupedFineZ_shuffle
    (m : ℕ)
    (g : MME.DWZTable2StandardForm.UsefulBlockShuffleGroup
      (groupedOuter (m := m)))
    (W : GroupedAllowedWords.{u} m)
    (p : GroupedPosition m) :
    groupedFineZ (solutionGroupedShuffleAllowedWords m g W) p =
      groupedFineZ W (g.1.symm p) := by
  rcases p with ⟨s, r⟩
  have hspec := solutionGroupedComponentPerm_spec m g⁻¹ s r
  have hspec' :
      g.1.symm ⟨s, r⟩ =
        ⟨s, solutionGroupedComponentPerm m g⁻¹ s r⟩ := hspec
  change
    let letter := PowIndex.get
      (MME.DWZTable2Counts.component s * m)
      (PowIndex.reindex
        (solutionGroupedComponentPerm m g⁻¹ s) (W s).1) r
    (letter.leftGrade, letter.rightGrade) =
      groupedFineZ W (g.1.symm ⟨s, r⟩)
  rw [PowIndex.get_reindex]
  change
    let letter := PowIndex.get
      (MME.DWZTable2Counts.component s * m) (W s).1
        (solutionGroupedComponentPerm m g⁻¹ s r)
    (letter.leftGrade, letter.rightGrade) =
      groupedFineZ W (g.1.symm ⟨s, r⟩)
  rw [hspec']
  rfl

private theorem solutionGroupedUsefulBlock_shuffle
    (m : ℕ)
    (g : MME.DWZTable2StandardForm.UsefulBlockShuffleGroup
      (groupedOuter (m := m)))
    (W : GroupedAllowedWords.{u} m) :
    groupedUsefulBlock m (solutionGroupedShuffleAllowedWords m g W) =
      MME.DWZTable2StandardForm.shuffleUsefulBlock m
        (groupedOuter (m := m)) g (groupedUsefulBlock m W) := by
  apply Subtype.ext
  funext p
  exact solutionGroupedFineZ_shuffle m g W p

theorem solution
    {K : Type u} [Field K] (m : ℕ)
    (g : MME.DWZTable2StandardForm.UsefulBlockShuffleGroup
      (groupedOuter (m := m))) :
    ∃ F : ∀ i : Fin 3,
        (TensorObj.kronFin 15
          (fun s : Fin 15 ↦ restrictedComponentPower K s m)).V i ≃ₗ[K]
        (TensorObj.kronFin 15
          (fun s : Fin 15 ↦ restrictedComponentPower K s m)).V i,
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
          (TensorObj.kronFin 15
            (fun s : Fin 15 ↦ restrictedComponentPower K s m)).t =
        (TensorObj.kronFin 15
          (fun s : Fin 15 ↦ restrictedComponentPower K s m)).t ∧
      ∀ W : GroupedAllowedWords.{u} m,
        ∃ W' : GroupedAllowedWords.{u} m,
          F 2 (TensorObj.kronFinModePiBasis 15
              (fun s : Fin 15 ↦ restrictedComponentPower K s m) 2
              (fun s ↦ restrictedComponentZBasis K s m) W) =
              TensorObj.kronFinModePiBasis 15
                (fun s : Fin 15 ↦ restrictedComponentPower K s m) 2
                (fun s ↦ restrictedComponentZBasis K s m) W' ∧
            groupedUsefulBlock m W' =
              MME.DWZTable2StandardForm.shuffleUsefulBlock m
                (groupedOuter (m := m)) g (groupedUsefulBlock m W) := by
  let e : ∀ s : Fin 15,
      Equiv.Perm (Fin (MME.DWZTable2Counts.component s * m)) :=
    fun s ↦ solutionGroupedComponentPerm m g⁻¹ s
  choose E hEtensor hEbasis using fun s : Fin 15 ↦
    mme_dwz_restricted_component_position_automorphism
      (K := K) s m (e s)
  let p : ∀ s : Fin 15, Equiv.Perm (AvailableComponentWord.{u} s m) :=
    fun s ↦ Equiv.subtypeEquiv (PowIndex.reindexEquiv (e s))
      (fun w ↦
        (mme_dwz_component_word_allowed_reindex_iff s m (e s) w).symm)
  have hEbasis' : ∀ (s : Fin 15) (w : AvailableComponentWord.{u} s m),
      E s 2 (restrictedComponentZBasis K s m w) =
        restrictedComponentZBasis K s m (p s w) := by
    intro s w
    exact hEbasis s w
  rcases mme_kronFin_modewise_basis_automorphisms_preserve_tensor
      (fun s : Fin 15 ↦ restrictedComponentPower K s m) 2
      (fun s ↦ restrictedComponentZBasis K s m) E p hEtensor hEbasis' with
    ⟨F, hFtensor, hFbasis⟩
  refine ⟨F, hFtensor, ?_⟩
  intro W
  refine ⟨solutionGroupedShuffleAllowedWords m g W, ?_,
    solutionGroupedUsefulBlock_shuffle m g W⟩
  exact hFbasis W
