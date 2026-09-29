-- Prove2me | solution 1 for mme_dwz_restricted_component_position_automorphism
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T10:04:20.011969+00:00
-- url     : https://prove2.me/submissions/f1787d11-4638-474c-804f-76fcd5795111

import Theorems.Thm_mme_kronPow_position_permutation_linear_equiv
import Theorems.Thm_mme_kronPow_position_permutation_recursive_basis
import Theorems.Thm_mme_dwz_restricted_component_Z_position_shuffle_inclusion_square
import Theorems.Thm_mme_dwz_component_word_allowed_reindex_iff
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_dwz_restricted_component_z_basis
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Position automorphisms of one restricted Table-2 component
-/

open MME MME.TensorObj MME.DWZComponentRestriction PiTensorProduct Module

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

private noncomputable def equivOnEqTop
    {K : Type u} [Field K] {V : Type u}
    [AddCommGroup V] [Module K V]
    (C : Submodule K V) (hC : C = ⊤) (P : V ≃ₗ[K] V) : C ≃ₗ[K] C := by
  have htop_le : (⊤ : Submodule K V) ≤ C := by
    rw [hC]
  exact
    { toFun := fun x ↦ ⟨P x.1, htop_le Submodule.mem_top⟩
      invFun := fun x ↦ ⟨P.symm x.1, htop_le Submodule.mem_top⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact P.symm_apply_apply x.1
      right_inv := by
        intro x
        apply Subtype.ext
        exact P.apply_symm_apply x.1
      map_add' := by
        intro x y
        apply Subtype.ext
        exact P.map_add x.1 y.1
      map_smul' := by
        intro a x
        apply Subtype.ext
        exact P.map_smul a x.1 }

private theorem equivOnEqTop_inclusion_square
    {K : Type u} [Field K] {V : Type u}
    [AddCommGroup V] [Module K V]
    (C : Submodule K V) (hC : C = ⊤) (P : V ≃ₗ[K] V) :
    C.subtype.comp (equivOnEqTop C hC P).toLinearMap =
      P.toLinearMap.comp C.subtype := by
  ext x
  rfl

private def componentModeShape (s : Fin 15) (i : Fin 3) : Fin 5 :=
  MME.cwSquareBlockType
    (MME.DWZSquare.shapeX s)
    (MME.DWZSquare.shapeY s)
    (MME.DWZSquare.shapeZ s) i

private noncomputable def canonicalComponentModeBasis
    (K : Type u) [Field K] (s : Fin 15) (i : Fin 3) :
    Basis (LiftedCoarsePair.{u} 6 (componentModeShape s i)) K
      ((canonicalComponentBlock K s).V i) :=
  (coarseClassBasis (K := K) 6 i (componentModeShape s i)).reindex
    Equiv.ulift.symm

private theorem canonicalComponentModeBasis_two
    (K : Type u) [Field K] (s : Fin 15) :
    canonicalComponentModeBasis K s 2 = canonicalComponentZBasis K s := by
  rfl

private theorem restrictedComponentZBasis_coe
    {K : Type u} [Field K] (s : Fin 15) (m : ℕ)
    (w : AvailableComponentWord.{u} s m) :
    (restrictedComponentZBasis K s m w).1 =
      componentPowerZBasis K s m w.1 := by
  let b := componentPowerZBasis K s m
  let v : AvailableComponentWord.{u} s m →
      (((canonicalComponentBlock K s).kronPow
        (MME.DWZTable2Counts.component s * m)).V 2) :=
    fun w ↦ b w.1
  have hv : LinearIndependent K v := by
    exact b.linearIndependent.comp
      (fun w : AvailableComponentWord.{u} s m ↦ w.1)
      Subtype.val_injective
  have hrange : Set.range v =
      b '' {w | componentWordAllowed s m w} := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w.1, w.2, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
  have hspan : Submodule.span K (Set.range v) =
      (componentPowerProjectionGrading K s m).classOf 2 0 := by
    rw [hrange]
    symm
    exact (mme_dwz_table2_component_projection_certificate
      (K := K) s m).2.2.2
  change ↑(((Basis.span hv).map (LinearEquiv.ofEq _ _ hspan)) w) = b w.1
  rw [Module.Basis.map_apply]
  change ↑((Basis.span hv) w) = b w.1
  rw [Module.Basis.span_apply]

/-- Every common permutation of the positions in one Table-2 component is
realized by modewise linear equivalences of the literal Z-restricted component
power, and these equivalences fix its tensor exactly. -/
theorem solution
    {K : Type u} [Field K]
    (s : Fin 15) (m : ℕ)
    (e : Equiv.Perm (Fin (MME.DWZTable2Counts.component s * m))) :
    ∃ Ψ : ∀ i : Fin 3,
        (restrictedComponentPower K s m).V i ≃ₗ[K]
          (restrictedComponentPower K s m).V i,
      PiTensorProduct.map (fun i ↦ (Ψ i).toLinearMap)
          (restrictedComponentPower K s m).t =
        (restrictedComponentPower K s m).t ∧
      ∀ w : AvailableComponentWord.{u} s m,
        Ψ 2 (restrictedComponentZBasis K s m w) =
          restrictedComponentZBasis K s m
            ⟨PowIndex.reindex e w.1,
              (mme_dwz_component_word_allowed_reindex_iff
                s m e w.1).2 w.2⟩ := by
  let : DecidablePred (componentWordAllowed s m) := Classical.decPred _
  let T := canonicalComponentBlock K s
  let n := MME.DWZTable2Counts.component s * m
  let b : ∀ i : Fin 3,
      Basis (LiftedCoarsePair.{u} 6 (componentModeShape s i)) K (T.V i) :=
    fun i ↦ canonicalComponentModeBasis K s i
  let P : ∀ i : Fin 3, (T.kronPow n).V i ≃ₗ[K] (T.kronPow n).V i :=
    fun i ↦ kronPowModePositionEquiv T i (b i) n e
  rcases mme_kronPow_position_permutation_linear_equiv T b n e with
    ⟨P', hP'basis, hP't⟩
  have hPP' : P' = P := by
    funext i
    apply LinearEquiv.toLinearMap_injective
    apply (kronPowModeWordBasis T i (b i) n).ext
    intro w
    change P' i (kronPowModeWordBasis T i (b i) n w) = _
    rw [hP'basis]
    exact (Basis.equiv_apply
      (b := kronPowModeWordBasis T i (b i) n)
      (i := w)
      (b' := kronPowModeWordBasis T i (b i) n)
      (e := kronPowWordReindex e
        (LiftedCoarsePair.{u} 6 (componentModeShape s i)))).symm
  have hPt :
      PiTensorProduct.map (fun i ↦ (P i).toLinearMap) (T.kronPow n).t =
        (T.kronPow n).t := by
    rw [← hPP']
    exact hP't
  let G := componentPowerProjectionGrading K s m
  have h0 : G.classOf 0 0 = ⊤ :=
    (mme_dwz_table2_component_projection_certificate (K := K) s m).2.1
  have h1 : G.classOf 1 0 = ⊤ :=
    (mme_dwz_table2_component_projection_certificate (K := K) s m).2.2.1
  let E0 : G.classOf 0 0 ≃ₗ[K] G.classOf 0 0 :=
    equivOnEqTop (G.classOf 0 0) h0 (P 0)
  let E1 : G.classOf 1 0 ≃ₗ[K] G.classOf 1 0 :=
    equivOnEqTop (G.classOf 1 0) h1 (P 1)
  rcases mme_dwz_restricted_component_Z_position_shuffle_inclusion_square
      (K := K) s m e with ⟨E2, hE2⟩
  let Ψ : ∀ i : Fin 3,
      (restrictedComponentPower K s m).V i ≃ₗ[K]
        (restrictedComponentPower K s m).V i :=
    Fin.cases E0 (fun j ↦
      Fin.cases E1 (fun k ↦
        Fin.cases E2 (fun z ↦ Fin.elim0 z) k) j)
  have hcomm0 :
      E0.toLinearMap.comp (G.blockProj 0 0) =
        (G.blockProj 0 0).comp (P 0).toLinearMap := by
    apply LinearMap.ext
    intro x
    change E0 (G.blockProj 0 0 x) = G.blockProj 0 0 (P 0 x)
    have hx : x ∈ G.classOf 0 0 := by
      rw [h0]
      exact Submodule.mem_top
    have hPx : P 0 x ∈ G.classOf 0 0 := by
      rw [h0]
      exact Submodule.mem_top
    rw [TensorObj.TypeGrading.blockProj_apply_mem G 0 0 x hx]
    rw [TensorObj.TypeGrading.blockProj_apply_mem G 0 0 (P 0 x) hPx]
    rfl
  have hcomm1 :
      E1.toLinearMap.comp (G.blockProj 1 0) =
        (G.blockProj 1 0).comp (P 1).toLinearMap := by
    apply LinearMap.ext
    intro x
    change E1 (G.blockProj 1 0 x) = G.blockProj 1 0 (P 1 x)
    have hx : x ∈ G.classOf 1 0 := by
      rw [h1]
      exact Submodule.mem_top
    have hPx : P 1 x ∈ G.classOf 1 0 := by
      rw [h1]
      exact Submodule.mem_top
    rw [TensorObj.TypeGrading.blockProj_apply_mem G 1 0 x hx]
    rw [TensorObj.TypeGrading.blockProj_apply_mem G 1 0 (P 1 x) hPx]
    rfl
  have hcomm2 :
      E2.toLinearMap.comp (G.blockProj 2 0) =
        (G.blockProj 2 0).comp (P 2).toLinearMap := by
    let bZ := componentPowerZBasis K s m
    apply bZ.ext
    intro w
    change E2 (G.blockProj 2 0 (bZ w)) =
      G.blockProj 2 0 (P 2 (bZ w))
    by_cases hw : componentWordAllowed s m w
    · have hw0 : bZ w ∈ G.classOf 2 0 := by
        rw [(mme_dwz_table2_component_projection_certificate
          (K := K) s m).2.2.2]
        exact Submodule.subset_span ⟨w, hw, rfl⟩
      have hrew : componentWordAllowed s m (PowIndex.reindex e w) :=
        (mme_dwz_component_word_allowed_reindex_iff s m e w).2 hw
      have hrew0 : bZ (PowIndex.reindex e w) ∈ G.classOf 2 0 := by
        rw [(mme_dwz_table2_component_projection_certificate
          (K := K) s m).2.2.2]
        exact Submodule.subset_span
          ⟨PowIndex.reindex e w, hrew, rfl⟩
      rw [TensorObj.TypeGrading.blockProj_apply_mem G 2 0 (bZ w) hw0]
      have hPbasis : P 2 (bZ w) = bZ (PowIndex.reindex e w) := by
        simp only [P, b, canonicalComponentModeBasis_two]
        exact mme_kronPow_position_permutation_recursive_basis
          T 2 (canonicalComponentZBasis K s) n e w
      rw [hPbasis]
      rw [TensorObj.TypeGrading.blockProj_apply_mem G 2 0
        (bZ (PowIndex.reindex e w)) hrew0]
      apply Subtype.ext
      have hz := DFunLike.congr_fun hE2 ⟨bZ w, hw0⟩
      change (E2 ⟨bZ w, hw0⟩).1 =
        kronPowModePositionEquiv T 2 (canonicalComponentZBasis K s)
          n e (bZ w) at hz
      have hzAction :
          kronPowModePositionEquiv T 2 (canonicalComponentZBasis K s)
              n e (bZ w) =
            bZ (PowIndex.reindex e w) := by
        simpa only [bZ, componentPowerZBasis, T, n] using
          (mme_kronPow_position_permutation_recursive_basis
            T 2 (canonicalComponentZBasis K s) n e w)
      rw [hzAction] at hz
      exact hz
    · have hw1 : bZ w ∈ G.classOf 2 1 := by
        change bZ w ∈ cwBasisGrade bZ
          (fun j ↦ if componentWordAllowed s m j then 0 else 1) 1
        exact Submodule.subset_span ⟨w, by simp [hw], rfl⟩
      have hrew : ¬ componentWordAllowed s m (PowIndex.reindex e w) := by
        intro h
        exact hw ((mme_dwz_component_word_allowed_reindex_iff s m e w).1 h)
      have hrew1 : bZ (PowIndex.reindex e w) ∈ G.classOf 2 1 := by
        change bZ (PowIndex.reindex e w) ∈ cwBasisGrade bZ
          (fun j ↦ if componentWordAllowed s m j then 0 else 1) 1
        exact Submodule.subset_span
          ⟨PowIndex.reindex e w, by simp [hrew], rfl⟩
      rw [TensorObj.TypeGrading.blockProj_apply_mem_ne G 2 0 1
        (by decide) (bZ w) hw1]
      have hPbasis : P 2 (bZ w) = bZ (PowIndex.reindex e w) := by
        simp only [P, b, canonicalComponentModeBasis_two]
        exact mme_kronPow_position_permutation_recursive_basis
          T 2 (canonicalComponentZBasis K s) n e w
      rw [hPbasis]
      rw [TensorObj.TypeGrading.blockProj_apply_mem_ne G 2 0 1
        (by decide) (bZ (PowIndex.reindex e w)) hrew1]
      exact map_zero E2
  have hcomm : ∀ i : Fin 3,
      (Ψ i).toLinearMap.comp (G.blockProj i 0) =
        (G.blockProj i 0).comp (P i).toLinearMap := by
    intro i
    fin_cases i
    · exact hcomm0
    · exact hcomm1
    · exact hcomm2
  refine ⟨Ψ, ?_, ?_⟩
  · change
      PiTensorProduct.map (fun i ↦ (Ψ i).toLinearMap)
          (PiTensorProduct.map (fun i ↦ G.blockProj i 0) (T.kronPow n).t) =
        PiTensorProduct.map (fun i ↦ G.blockProj i 0) (T.kronPow n).t
    have h1 :
        PiTensorProduct.map (fun i ↦ (Ψ i).toLinearMap)
            (PiTensorProduct.map (fun i ↦ G.blockProj i 0)
              (T.kronPow n).t) =
          PiTensorProduct.map
            (fun i ↦ (Ψ i).toLinearMap.comp (G.blockProj i 0))
            (T.kronPow n).t :=
      (congrFun (congrArg DFunLike.coe
        (PiTensorProduct.map_comp (fun i ↦ (Ψ i).toLinearMap)
          (fun i ↦ G.blockProj i 0))) _).symm
    have h2 := congrArg
      (fun F ↦ PiTensorProduct.map F (T.kronPow n).t) (funext hcomm)
    have h3 :
        PiTensorProduct.map
            (fun i ↦ (G.blockProj i 0).comp (P i).toLinearMap)
            (T.kronPow n).t =
          PiTensorProduct.map (fun i ↦ G.blockProj i 0)
            (PiTensorProduct.map (fun i ↦ (P i).toLinearMap)
              (T.kronPow n).t) :=
      congrFun (congrArg DFunLike.coe
        (PiTensorProduct.map_comp (fun i ↦ G.blockProj i 0)
          (fun i ↦ (P i).toLinearMap))) _
    have h4 := congrArg
      (fun x ↦ PiTensorProduct.map (fun i ↦ G.blockProj i 0) x) hPt
    exact h1.trans (h2.trans (h3.trans h4))
  · intro w
    let w' : AvailableComponentWord.{u} s m :=
      ⟨PowIndex.reindex e w.1,
        (mme_dwz_component_word_allowed_reindex_iff s m e w.1).2 w.2⟩
    let bZ := componentPowerZBasis K s m
    have hw0 : bZ w.1 ∈ G.classOf 2 0 := by
      rw [(mme_dwz_table2_component_projection_certificate
        (K := K) s m).2.2.2]
      exact Submodule.subset_span ⟨w.1, w.2, rfl⟩
    have hw'0 : bZ w'.1 ∈ G.classOf 2 0 := by
      rw [(mme_dwz_table2_component_projection_certificate
        (K := K) s m).2.2.2]
      exact Submodule.subset_span ⟨w'.1, w'.2, rfl⟩
    have hb : restrictedComponentZBasis K s m w =
        ⟨bZ w.1, hw0⟩ := by
      apply Subtype.ext
      exact restrictedComponentZBasis_coe s m w
    have hb' : restrictedComponentZBasis K s m w' =
        ⟨bZ w'.1, hw'0⟩ := by
      apply Subtype.ext
      exact restrictedComponentZBasis_coe s m w'
    change Ψ 2 (restrictedComponentZBasis K s m w) =
      restrictedComponentZBasis K s m w'
    rw [hb, hb']
    change E2 ⟨bZ w.1, hw0⟩ = ⟨bZ w'.1, hw'0⟩
    apply Subtype.ext
    have hz := DFunLike.congr_fun hE2 ⟨bZ w.1, hw0⟩
    change (E2 ⟨bZ w.1, hw0⟩).1 =
      kronPowModePositionEquiv T 2 (canonicalComponentZBasis K s)
        n e (bZ w.1) at hz
    have hzAction :
        kronPowModePositionEquiv T 2 (canonicalComponentZBasis K s)
            n e (bZ w.1) =
          bZ (PowIndex.reindex e w.1) := by
      simpa only [bZ, componentPowerZBasis, T, n] using
        (mme_kronPow_position_permutation_recursive_basis
          T 2 (canonicalComponentZBasis K s) n e w.1)
    exact hz.trans (by simpa only [w'] using hzAction)
