-- Prove2me | solution 1 for mme_dwz_source_coarse_address_to_raw_component_powers_exact_Z_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T09:04:12.00268+00:00
-- url     : https://prove2.me/submissions/bf2b5079-d52a-4709-abe3-cae4f71720a8

import Definitions.Def_mme_kronFin_rec_group_position_equiv_data
import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Definitions.Def_mme_dwz_canonical_component_row_cast_data
import Definitions.Def_mme_dwz_restricted_component_z_basis
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_dwz_source_aligned_broken_obj
import Theorems.Thm_mme_kronFin_reindex_equiv_preserves_tensor_and_basis
import Theorems.Thm_mme_kronFin_rec_groups_preserves_tensor_and_basis
import Theorems.Thm_mme_kronFin_const_pow_preserves_tensor_and_basis
import Theorems.Thm_mme_kronFin_recGroupWord_at_position
import Theorems.Thm_mme_kronFin_recGroupModeCast_basis
import Theorems.Thm_mme_dwz_canonical_component_row_cast_exact

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 10000

namespace MME.DWZSourceAligned

private noncomputable def groupedPositionEquivOfHistogramExact
    {N m : ℕ} (outer : Fin N → Fin 15)
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        DWZTable2Counts.component s * m) :
    DWZComponentRestriction.GroupedPosition m ≃ Fin N := by
  let fiberEquiv : ∀ s : Fin 15,
      Fin (DWZTable2Counts.component s * m) ≃
        {r : Fin N // outer r = s} := fun s ↦
    Fintype.equivOfCardEq (by simpa using (houter s).symm)
  exact (Equiv.sigmaCongrRight fiberEquiv).trans
    (Equiv.sigmaFiberEquiv outer)

private theorem groupedPositionEquivOfHistogramExact_outer
    {N m : ℕ} (outer : Fin N → Fin 15)
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        DWZTable2Counts.component s * m)
    (p : DWZComponentRestriction.GroupedPosition m) :
    outer (groupedPositionEquivOfHistogramExact outer houter p) =
      DWZComponentRestriction.groupedOuter p := by
  rcases p with ⟨s, r⟩
  change outer
      (((Fintype.equivOfCardEq _ :
        Fin (DWZTable2Counts.component s * m) ≃
          {r : Fin N // outer r = s}) r).1) = s
  exact ((Fintype.equivOfCardEq _ :
    Fin (DWZTable2Counts.component s * m) ≃
      {r : Fin N // outer r = s}) r).2

private theorem table2_histogram_two_le_length_exact
    {N m : ℕ} (outer : Fin N → Fin 15)
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        DWZTable2Counts.component s * m)
    (hm : 0 < m) : 2 ≤ N := by
  have hsub : Fintype.card {r : Fin N // outer r = (0 : Fin 15)} ≤ N :=
    by simpa using (Fintype.card_subtype_le
      (fun r : Fin N ↦ outer r = (0 : Fin 15)))
  rw [houter 0] at hsub
  norm_num [DWZTable2Counts.component] at hsub
  omega

private theorem tensorObj_eq_mode_cast_preserves_exact
    {K : Type u} [Field K] {d : ℕ} {X Y : TensorObj K d}
    (h : X = Y) :
    PiTensorProduct.map
        (fun i ↦ (LinearEquiv.cast (R := K)
          (M := fun U : TensorObj K d ↦ U.V i) h).toLinearMap) X.t =
      Y.t := by
  subst Y
  change PiTensorProduct.map (fun _ : Fin d ↦ LinearMap.id) X.t = X.t
  rw [PiTensorProduct.map_id]
  rfl

private theorem eqCast_heq_raw
    {A B : Type u} (h : A = B) (x : A) : HEq (h ▸ x) x := by
  subst B
  rfl

/-- The literal source-order coarse address can be regrouped into the fifteen
raw Table-2 component powers.  Besides preserving the tensor, the map sends
every canonical Z word to the exact grouped product-basis word, and every
grouped letter is heterogeneously equal to the original letter at the
corresponding source position. -/
theorem sourceCoarseAddress_to_rawComponentPowers_exact_Z_basis
    {K : Type u} [Field K] {N m : ℕ}
    (outer : Fin N → Fin 15)
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        DWZTable2Counts.component s * m)
    (hm : 0 < m) :
    ∃ e : DWZComponentRestriction.GroupedPosition m ≃ Fin N,
      (∀ p, outer (e p) = DWZComponentRestriction.groupedOuter p) ∧
      ∃ f : ∀ i : Fin 3,
          (coarseAddressObj K outer).V i →ₗ[K]
            (TensorObj.kronFin 15 (fun s ↦
              (DWZComponentRestriction.canonicalComponentBlock K s).kronPow
                (DWZTable2Counts.component s * m))).V i,
        PiTensorProduct.map f (coarseAddressObj K outer).t =
          (TensorObj.kronFin 15 (fun s ↦
            (DWZComponentRestriction.canonicalComponentBlock K s).kronPow
              (DWZTable2Counts.component s * m))).t ∧
        ∀ W : AddressZWord.{u} outer,
          ∃ raw : ∀ s : Fin 15,
              DWZComponentRestriction.PowIndex
                (DWZComponentRestriction.LiftedCoarsePair.{u} 6
                  (DWZSquare.shapeZ s))
                (DWZTable2Counts.component s * m),
            (∀ p : DWZComponentRestriction.GroupedPosition m,
              HEq (DWZComponentRestriction.PowIndex.get
                  (DWZTable2Counts.component p.1 * m) (raw p.1) p.2)
                (W (e p))) ∧
            f 2 (coarseAddressZBasis K outer W) =
              TensorObj.kronFinModePiBasis 15
                (fun s ↦
                  (DWZComponentRestriction.canonicalComponentBlock K s).kronPow
                    (DWZTable2Counts.component s * m)) 2
                (fun s ↦
                  DWZComponentRestriction.componentPowerZBasis K s m) raw := by
  let count : Fin 15 → ℕ := fun s ↦
    DWZTable2Counts.component s * m
  let component : Fin 15 → TensorObj K 3 := fun s ↦
    DWZComponentRestriction.canonicalComponentBlock K s
  let zIndex : Fin 15 → Type u := fun s ↦
    DWZComponentRestriction.LiftedCoarsePair.{u} 6
      (DWZSquare.shapeZ s)
  let zBasis : ∀ s, Basis (zIndex s) K ((component s).V 2) := fun s ↦
    DWZComponentRestriction.canonicalComponentZBasis K s
  let flat : Fin (TensorObj.recGroupLength 15 count) → TensorObj K 3 :=
    TensorObj.recGroupFamily 15 count component
  let flatIndex : Fin (TensorObj.recGroupLength 15 count) → Type u :=
    TensorObj.recGroupFamily 15 count zIndex
  let flatBasis : ∀ r, Basis (flatIndex r) K ((flat r).V 2) :=
    TensorObj.recGroupBasisFamily 15 count component 2 zIndex zBasis
  let nested : Fin 15 → TensorObj K 3 := fun s ↦
    TensorObj.kronFin (count s) (fun _ ↦ component s)
  let rawObj : Fin 15 → TensorObj K 3 := fun s ↦
    (component s).kronPow (count s)
  let eGrouped : DWZComponentRestriction.GroupedPosition m ≃ Fin N :=
    groupedPositionEquivOfHistogramExact outer houter
  let eFlat : Fin (TensorObj.recGroupLength 15 count) ≃ Fin N :=
    (TensorObj.recGroupPositionEquiv 15 count).trans eGrouped
  have heGrouped : ∀ p, outer (eGrouped p) =
      DWZComponentRestriction.groupedOuter p := by
    intro p
    exact groupedPositionEquivOfHistogramExact_outer outer houter p
  have heFlat : ∀ r, outer (eFlat r) =
      (TensorObj.recGroupPositionEquiv 15 count r).1 := by
    intro r
    exact heGrouped (TensorObj.recGroupPositionEquiv 15 count r)
  let sourceFamily : Fin N → TensorObj K 3 := fun r ↦
    component (outer r)
  let sourceIndex : Fin N → Type u := fun r ↦ zIndex (outer r)
  let sourceBasis : ∀ r, Basis (sourceIndex r) K ((sourceFamily r).V 2) :=
    fun r ↦ zBasis (outer r)
  let reordered : Fin (TensorObj.recGroupLength 15 count) → TensorObj K 3 :=
    fun r ↦ sourceFamily (eFlat r)
  let reorderedIndex : Fin (TensorObj.recGroupLength 15 count) → Type u :=
    fun r ↦ sourceIndex (eFlat r)
  let reorderedBasis : ∀ r,
      Basis (reorderedIndex r) K ((reordered r).V 2) :=
    fun r ↦ sourceBasis (eFlat r)
  have hflatTwo : 2 ≤ TensorObj.recGroupLength 15 count := by
    have hcard : TensorObj.recGroupLength 15 count = N := by
      simpa [eFlat] using Fintype.card_congr eFlat
    have hN := table2_histogram_two_le_length_exact outer houter hm
    omega
  obtain ⟨P, hPtensor, hPbasis⟩ :=
    mme_kronFin_reindex_equiv_preserves_tensor_and_basis
      (K := K) (d := 3) hflatTwo sourceFamily eFlat
  let rowCast : ∀ r i, (reordered r).V i ≃ₗ[K]
      (component (TensorObj.recGroupPositionEquiv 15 count r).1).V i :=
    fun r i ↦ canonicalComponentModeCast (K := K) (heFlat r) i
  let groupCast : ∀ r i,
      (component (TensorObj.recGroupPositionEquiv 15 count r).1).V i ≃ₗ[K]
        (flat r).V i := fun r i ↦
    LinearEquiv.cast (R := K)
      (M := fun U : TensorObj K 3 ↦ U.V i)
      (TensorObj.recGroupFamily_at_position 15 count component r).symm
  let factorCast : ∀ r i, (reordered r).V i →ₗ[K] (flat r).V i :=
    fun r i ↦ (groupCast r i).toLinearMap.comp
      (rowCast r i).toLinearMap
  have hfactorTensor : ∀ r,
      PiTensorProduct.map (factorCast r) (reordered r).t = (flat r).t := by
    intro r
    have hrow := (mme_dwz_canonical_component_row_cast_exact
      (K := K) (heFlat r)).1
    have hgroup := tensorObj_eq_mode_cast_preserves_exact
      (TensorObj.recGroupFamily_at_position 15 count component r).symm
    calc
      PiTensorProduct.map (factorCast r) (reordered r).t =
          PiTensorProduct.map (fun i ↦ (groupCast r i).toLinearMap)
            (PiTensorProduct.map (fun i ↦ (rowCast r i).toLinearMap)
              (reordered r).t) := by
        rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
      _ = (flat r).t := by rw [hrow, hgroup]
  have hCtensor :
      PiTensorProduct.map
          (TensorObj.kronFinFamilyModeMap
            (TensorObj.recGroupLength 15 count) reordered flat factorCast)
          (TensorObj.kronFin (TensorObj.recGroupLength 15 count) reordered).t =
        (TensorObj.kronFin (TensorObj.recGroupLength 15 count) flat).t := by
    exact TensorObj.kronFinFamilyModeMap_preserves_tensor
      reordered flat factorCast hfactorTensor
  obtain ⟨hGtensor, hGbasis⟩ :=
    mme_kronFin_rec_groups_preserves_tensor_and_basis 15 count component
  have hPowTensor :
      PiTensorProduct.map
          (TensorObj.kronFinFamilyModeMap 15 nested rawObj
            (fun s i ↦
              (TensorObj.kronFinConstPowModeEquiv (component s) i
                (count s)).toLinearMap))
          (TensorObj.kronFin 15 nested).t =
        (TensorObj.kronFin 15 rawObj).t := by
    apply TensorObj.kronFinFamilyModeMap_preserves_tensor
    intro s
    exact (mme_kronFin_const_pow_preserves_tensor_and_basis
      (component s) (count s)).1
  have hPinvTensor :
      PiTensorProduct.map (fun i ↦ (P i).symm.toLinearMap)
          (TensorObj.kronFin N sourceFamily).t =
        (TensorObj.kronFin (TensorObj.recGroupLength 15 count) reordered).t := by
    rw [← hPtensor]
    rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    have hcomp :
        (fun i ↦ (P i).symm.toLinearMap ∘ₗ (P i).toLinearMap) =
          (fun _ : Fin 3 ↦ LinearMap.id) := by
      funext i
      ext x
      simp
    rw [hcomp, PiTensorProduct.map_id]
    rfl
  let f : ∀ i : Fin 3, (coarseAddressObj K outer).V i →ₗ[K]
      (TensorObj.kronFin 15 rawObj).V i := fun i ↦
    (TensorObj.kronFinFamilyModeMap 15 nested rawObj
      (fun s j ↦
        (TensorObj.kronFinConstPowModeEquiv (component s) j
          (count s)).toLinearMap) i).comp
      ((TensorObj.kronFinRecGroupsModeEquiv 15 count component i).toLinearMap.comp
        ((TensorObj.kronFinFamilyModeMap
          (TensorObj.recGroupLength 15 count) reordered flat factorCast i).comp
          (P i).symm.toLinearMap))
  refine ⟨eGrouped, heGrouped, f, ?_, ?_⟩
  · change PiTensorProduct.map f (TensorObj.kronFin N sourceFamily).t =
      (TensorObj.kronFin 15 rawObj).t
    rw [show PiTensorProduct.map f =
        PiTensorProduct.map
            (TensorObj.kronFinFamilyModeMap 15 nested rawObj
              (fun s i ↦
                (TensorObj.kronFinConstPowModeEquiv (component s) i
                  (count s)).toLinearMap)) ∘ₗ
          PiTensorProduct.map
            (fun i ↦
              (TensorObj.kronFinRecGroupsModeEquiv 15 count component i).toLinearMap ∘ₗ
                ((TensorObj.kronFinFamilyModeMap
                    (TensorObj.recGroupLength 15 count) reordered flat
                    factorCast i) ∘ₗ (P i).symm.toLinearMap)) by
      rw [← PiTensorProduct.map_comp]
      rfl]
    change PiTensorProduct.map
        (TensorObj.kronFinFamilyModeMap 15 nested rawObj
          (fun s i ↦
            (TensorObj.kronFinConstPowModeEquiv (component s) i
              (count s)).toLinearMap))
      (PiTensorProduct.map
        (fun i ↦
          (TensorObj.kronFinRecGroupsModeEquiv 15 count component i).toLinearMap ∘ₗ
            ((TensorObj.kronFinFamilyModeMap
                (TensorObj.recGroupLength 15 count) reordered flat
                factorCast i) ∘ₗ (P i).symm.toLinearMap))
        (TensorObj.kronFin N sourceFamily).t) = _
    rw [show PiTensorProduct.map
          (fun i ↦
            (TensorObj.kronFinRecGroupsModeEquiv 15 count component i).toLinearMap ∘ₗ
              ((TensorObj.kronFinFamilyModeMap
                  (TensorObj.recGroupLength 15 count) reordered flat
                  factorCast i) ∘ₗ (P i).symm.toLinearMap)) =
        PiTensorProduct.map
            (fun i ↦
              (TensorObj.kronFinRecGroupsModeEquiv 15 count component i).toLinearMap) ∘ₗ
          PiTensorProduct.map
            (fun i ↦
              (TensorObj.kronFinFamilyModeMap
                (TensorObj.recGroupLength 15 count) reordered flat
                factorCast i) ∘ₗ (P i).symm.toLinearMap) by
      simpa only [LinearMap.comp_assoc] using
        (PiTensorProduct.map_comp
          (g := fun i ↦
            (TensorObj.kronFinRecGroupsModeEquiv 15 count component i).toLinearMap)
          (f := fun i ↦
            (TensorObj.kronFinFamilyModeMap
              (TensorObj.recGroupLength 15 count) reordered flat
              factorCast i) ∘ₗ (P i).symm.toLinearMap))]
    change PiTensorProduct.map
        (TensorObj.kronFinFamilyModeMap 15 nested rawObj
          (fun s i ↦
            (TensorObj.kronFinConstPowModeEquiv (component s) i
              (count s)).toLinearMap))
      (PiTensorProduct.map
        (fun i ↦
          (TensorObj.kronFinRecGroupsModeEquiv 15 count component i).toLinearMap)
        (PiTensorProduct.map
          (fun i ↦
            (TensorObj.kronFinFamilyModeMap
              (TensorObj.recGroupLength 15 count) reordered flat
              factorCast i) ∘ₗ (P i).symm.toLinearMap)
          (TensorObj.kronFin N sourceFamily).t)) = _
    rw [show PiTensorProduct.map
          (fun i ↦
            (TensorObj.kronFinFamilyModeMap
              (TensorObj.recGroupLength 15 count) reordered flat
              factorCast i) ∘ₗ (P i).symm.toLinearMap) =
        PiTensorProduct.map
            (TensorObj.kronFinFamilyModeMap
              (TensorObj.recGroupLength 15 count) reordered flat factorCast) ∘ₗ
          PiTensorProduct.map (fun i ↦ (P i).symm.toLinearMap) by
      simpa only [LinearMap.comp_assoc] using
        (PiTensorProduct.map_comp
          (g := TensorObj.kronFinFamilyModeMap
            (TensorObj.recGroupLength 15 count) reordered flat factorCast)
          (f := fun i ↦ (P i).symm.toLinearMap))]
    change PiTensorProduct.map
        (TensorObj.kronFinFamilyModeMap 15 nested rawObj
          (fun s i ↦
            (TensorObj.kronFinConstPowModeEquiv (component s) i
              (count s)).toLinearMap))
      (PiTensorProduct.map
        (fun i ↦
          (TensorObj.kronFinRecGroupsModeEquiv 15 count component i).toLinearMap)
        (PiTensorProduct.map
          (TensorObj.kronFinFamilyModeMap
            (TensorObj.recGroupLength 15 count) reordered flat factorCast)
          (PiTensorProduct.map (fun i ↦ (P i).symm.toLinearMap)
            (TensorObj.kronFin N sourceFamily).t))) = _
    rw [hPinvTensor, hCtensor, hGtensor, hPowTensor]
  · intro W
    let wReordered : ∀ r, reorderedIndex r :=
      (Equiv.piCongrLeft sourceIndex eFlat).symm W
    let rowLetter : ∀ r, zIndex
        (TensorObj.recGroupPositionEquiv 15 count r).1 := fun r ↦
      canonicalComponentZLetterCast (heFlat r) (wReordered r)
    let hIndex : ∀ r,
        zIndex (TensorObj.recGroupPositionEquiv 15 count r).1 =
          flatIndex r := fun r ↦
      (TensorObj.recGroupFamily_at_position 15 count zIndex r).symm
    let wFlat : ∀ r, flatIndex r := fun r ↦ hIndex r ▸ rowLetter r
    let groupedWord : ∀ s, Fin (count s) → zIndex s :=
      TensorObj.recGroupWord wFlat
    let raw : ∀ s : Fin 15,
        DWZComponentRestriction.PowIndex (zIndex s) (count s) := fun s ↦
      DWZComponentRestriction.PowIndex.ofFun (count s) (groupedWord s)
    refine ⟨raw, ?_, ?_⟩
    · intro p
      rw [DWZComponentRestriction.PowIndex.get_ofFun]
      have hrec := mme_kronFin_recGroupWord_at_position wFlat p
      let r := (TensorObj.recGroupPositionEquiv 15 count).symm p
      have hflatLetter : HEq (wFlat r) (wReordered r) := by
        have h1 : HEq (hIndex r ▸ rowLetter r) (rowLetter r) :=
          eqCast_heq_raw (hIndex r) (rowLetter r)
        have h2 : HEq (rowLetter r) (wReordered r) :=
          (mme_dwz_canonical_component_row_cast_exact
            (K := K) (heFlat r)).2.2 (wReordered r)
        exact h1.trans h2
      have hpi : wReordered r = W (eFlat r) := by
        exact Equiv.piCongrLeft_symm_apply sourceIndex eFlat W r
      have he : eFlat r = eGrouped p := by
        change eGrouped
            (TensorObj.recGroupPositionEquiv 15 count r) = eGrouped p
        rw [show TensorObj.recGroupPositionEquiv 15 count r = p by
          exact (TensorObj.recGroupPositionEquiv 15 count).apply_symm_apply p]
      have heW : HEq (W (eFlat r)) (W (eGrouped p)) := by
        rw [he]
      exact hrec.trans (hflatLetter.trans
        ((heq_of_eq hpi).trans heW))
    · have hPinvBasis :
          (P 2).symm (coarseAddressZBasis K outer W) =
            TensorObj.kronFinModePiBasis
              (TensorObj.recGroupLength 15 count) reordered 2
              reorderedBasis wReordered := by
        change (P 2).symm
            (TensorObj.kronFinModePiBasis N sourceFamily 2 sourceBasis W) = _
        have hp := hPbasis 2 sourceIndex sourceBasis wReordered
        have hw : Equiv.piCongrLeft sourceIndex eFlat wReordered = W :=
          Equiv.apply_symm_apply (Equiv.piCongrLeft sourceIndex eFlat) W
        rw [hw] at hp
        rw [← hp]
        simp
        rfl
      have hFactorBasis : ∀ r x,
          factorCast r 2 (reorderedBasis r x) = flatBasis r (hIndex r ▸
            canonicalComponentZLetterCast (heFlat r) x) := by
        intro r x
        change (groupCast r 2)
            (rowCast r 2 (reorderedBasis r x)) = _
        have hrow := (mme_dwz_canonical_component_row_cast_exact
          (K := K) (heFlat r)).2.1 x
        rw [eq_of_heq hrow]
        exact mme_kronFin_recGroupModeCast_basis count component 2 zIndex zBasis
          r (canonicalComponentZLetterCast (heFlat r) x)
      have hCBasis :
          TensorObj.kronFinFamilyModeMap
              (TensorObj.recGroupLength 15 count) reordered flat factorCast 2
              (TensorObj.kronFinModePiBasis
                (TensorObj.recGroupLength 15 count) reordered 2
                reorderedBasis wReordered) =
            TensorObj.kronFinModePiBasis
              (TensorObj.recGroupLength 15 count) flat 2 flatBasis wFlat := by
        exact TensorObj.kronFinFamilyModeMap_basis reordered flat 2
          reorderedBasis flatBasis factorCast
          (fun r x ↦ hIndex r ▸
            canonicalComponentZLetterCast (heFlat r) x)
          hFactorBasis wReordered
      have hGBasis := hGbasis 2 zIndex zBasis wFlat
      have hPowBasis :
          TensorObj.kronFinFamilyModeMap 15 nested rawObj
              (fun s i ↦
                (TensorObj.kronFinConstPowModeEquiv (component s) i
                  (count s)).toLinearMap) 2
              (TensorObj.kronFinModePiBasis 15 nested 2
                (fun s ↦ TensorObj.kronFinModePiBasis (count s)
                  (fun _ ↦ component s) 2 (fun _ ↦ zBasis s)) groupedWord) =
            TensorObj.kronFinModePiBasis 15 rawObj 2
              (fun s ↦ DWZComponentRestriction.componentPowerZBasis K s m)
              raw := by
        exact TensorObj.kronFinFamilyModeMap_basis nested rawObj 2
          (fun s ↦ TensorObj.kronFinModePiBasis (count s)
            (fun _ ↦ component s) 2 (fun _ ↦ zBasis s))
          (fun s ↦ DWZComponentRestriction.componentPowerZBasis K s m)
          (fun s i ↦
            (TensorObj.kronFinConstPowModeEquiv (component s) i
              (count s)).toLinearMap)
          (fun s w ↦ DWZComponentRestriction.PowIndex.ofFun (count s) w)
          (fun s w ↦
            (mme_kronFin_const_pow_preserves_tensor_and_basis
              (component s) (count s)).2 2 (zBasis s) w)
          groupedWord
      change f 2 (coarseAddressZBasis K outer W) = _
      unfold f
      simp only [LinearMap.comp_apply]
      let post :
          (TensorObj.kronFin (TensorObj.recGroupLength 15 count) reordered).V 2 →
            (TensorObj.kronFin 15 rawObj).V 2 := fun x ↦
        TensorObj.kronFinFamilyModeMap 15 nested rawObj
          (fun s j ↦
            (TensorObj.kronFinConstPowModeEquiv (component s) j
              (count s)).toLinearMap) 2
          ((TensorObj.kronFinRecGroupsModeEquiv 15 count component 2)
            (TensorObj.kronFinFamilyModeMap
              (TensorObj.recGroupLength 15 count) reordered flat
              factorCast 2 x))
      change post ((P 2).symm (coarseAddressZBasis K outer W)) = _
      rw [hPinvBasis]
      dsimp only [post]
      rw [hCBasis, hGBasis, hPowBasis]

end MME.DWZSourceAligned

open MME.DWZSourceAligned

theorem solution
    {K : Type u} [Field K] {N m : ℕ}
    (outer : Fin N → Fin 15)
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        MME.DWZTable2Counts.component s * m)
    (hm : 0 < m) :
    ∃ e : MME.DWZComponentRestriction.GroupedPosition m ≃ Fin N,
      (∀ p, outer (e p) =
        MME.DWZComponentRestriction.groupedOuter p) ∧
      ∃ f : ∀ i : Fin 3,
          (coarseAddressObj K outer).V i →ₗ[K]
            (MME.TensorObj.kronFin 15 (fun s ↦
              (MME.DWZComponentRestriction.canonicalComponentBlock K s).kronPow
                (MME.DWZTable2Counts.component s * m))).V i,
        PiTensorProduct.map f (coarseAddressObj K outer).t =
          (MME.TensorObj.kronFin 15 (fun s ↦
            (MME.DWZComponentRestriction.canonicalComponentBlock K s).kronPow
              (MME.DWZTable2Counts.component s * m))).t ∧
        ∀ W : AddressZWord.{u} outer,
          ∃ raw : ∀ s : Fin 15,
              MME.DWZComponentRestriction.PowIndex
                (MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6
                  (MME.DWZSquare.shapeZ s))
                (MME.DWZTable2Counts.component s * m),
            (∀ p : MME.DWZComponentRestriction.GroupedPosition m,
              HEq (MME.DWZComponentRestriction.PowIndex.get
                  (MME.DWZTable2Counts.component p.1 * m) (raw p.1) p.2)
                (W (e p))) ∧
            f 2 (coarseAddressZBasis K outer W) =
              MME.TensorObj.kronFinModePiBasis 15
                (fun s ↦
                  (MME.DWZComponentRestriction.canonicalComponentBlock K s).kronPow
                    (MME.DWZTable2Counts.component s * m)) 2
                (fun s ↦
                  MME.DWZComponentRestriction.componentPowerZBasis K s m) raw := by
  exact sourceCoarseAddress_to_rawComponentPowers_exact_Z_basis
    outer houter hm
