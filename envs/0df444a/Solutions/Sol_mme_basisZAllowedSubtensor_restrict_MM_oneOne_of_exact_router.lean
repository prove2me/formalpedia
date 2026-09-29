-- Prove2me | solution 1 for mme_basisZAllowedSubtensor_restrict_MM_oneOne_of_exact_router
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T07:03:51.517038+00:00
-- url     : https://prove2.me/submissions/4266d633-a85c-4fe6-b128-ae6923d90901

import Mathlib
import Definitions.Def_mme_basis_z_allowed_projection
import Theorems.Thm_mme_restrict_basisZAllowedSubtensor_of_vanishes

open PiTensorProduct BigOperators
open MME Module

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace MME.DWZBalancedRectangular

/-! ## Coordinate projectors for the two rectangular orientations -/

private noncomputable def oneOneProjector
    {K : Type u} [Field K] {D P : ℕ} (e : Fin D ↪ Fin P) :
    ∀ s : Fin 3, (MMObj K 1 1 P).V s →ₗ[K] (MMObj K 1 1 D).V s
  | ⟨0, _⟩ => LinearMap.funLeft K K (fun ab : Fin 1 × Fin 1 ↦ ab)
  | ⟨1, _⟩ =>
      LinearMap.funLeft K K (fun ab : Fin 1 × Fin D ↦ (ab.1, e ab.2))
  | ⟨2, _⟩ =>
      LinearMap.funLeft K K (fun ab : Fin D × Fin 1 ↦ (e ab.1, ab.2))

private noncomputable def firstProjector
    {K : Type u} [Field K] {D P : ℕ} (e : Fin D ↪ Fin P) :
    ∀ s : Fin 3, (MMObj K P 1 1).V s →ₗ[K] (MMObj K D 1 1).V s
  | ⟨0, _⟩ =>
      LinearMap.funLeft K K (fun ab : Fin D × Fin 1 ↦ (e ab.1, ab.2))
  | ⟨1, _⟩ => LinearMap.funLeft K K (fun ab : Fin 1 × Fin 1 ↦ ab)
  | ⟨2, _⟩ =>
      LinearMap.funLeft K K (fun ab : Fin 1 × Fin D ↦ (ab.1, e ab.2))

private noncomputable def oneOnePure
    (K : Type u) [Field K] (P : ℕ) (k : Fin P) :
    PiTensorProduct K (MMSpace K 1 1 P) :=
  tprod K (fun s : Fin 3 ↦
    match s with
    | ⟨0, _⟩ =>
        (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 : Fin 1 × Fin 1 → K)
    | ⟨1, _⟩ =>
        (Pi.single ((0 : Fin 1), k) 1 : Fin 1 × Fin P → K)
    | ⟨2, _⟩ =>
        (Pi.single (k, (0 : Fin 1)) 1 : Fin P × Fin 1 → K))

private noncomputable def firstPure
    (K : Type u) [Field K] (P : ℕ) (k : Fin P) :
    PiTensorProduct K (MMSpace K P 1 1) :=
  tprod K (fun s : Fin 3 ↦
    match s with
    | ⟨0, _⟩ =>
        (Pi.single (k, (0 : Fin 1)) 1 : Fin P × Fin 1 → K)
    | ⟨1, _⟩ =>
        (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 : Fin 1 × Fin 1 → K)
    | ⟨2, _⟩ =>
        (Pi.single ((0 : Fin 1), k) 1 : Fin 1 × Fin P → K))

private theorem oneOneTensor_eq_sum_pure
    (K : Type u) [Field K] (P : ℕ) :
    (MMObj K 1 1 P).t = ∑ k : Fin P, oneOnePure K P k := by
  change MMTensor K 1 1 P = _
  simp only [MMTensor, Fin.sum_univ_one]
  rfl

private theorem firstTensor_eq_sum_pure
    (K : Type u) [Field K] (P : ℕ) :
    (MMObj K P 1 1).t = ∑ k : Fin P, firstPure K P k := by
  change MMTensor K P 1 1 = _
  simp only [MMTensor, Fin.sum_univ_one]
  rfl

private theorem funLeft_single_of_injective
    (K : Type u) [Field K] {A B : Type*}
    [DecidableEq A] [DecidableEq B]
    (f : B → A) (hf : Function.Injective f) (b : B) :
    LinearMap.funLeft K K f (Pi.single (f b) 1) =
      (Pi.single b 1 : B → K) := by
  classical
  funext x
  simp only [LinearMap.funLeft_apply, Pi.single_apply, hf.eq_iff]

private theorem funLeft_single_outside
    (K : Type u) [Field K] {A B : Type*}
    [DecidableEq A] (f : B → A) (a : A)
    (h : ∀ b, f b ≠ a) :
    LinearMap.funLeft K K f (Pi.single a 1) = (0 : B → K) := by
  funext b
  simp [LinearMap.funLeft_apply, h b]

private theorem oneOneProjector_map_selected
    {K : Type u} [Field K] {D P : ℕ}
    (e : Fin D ↪ Fin P) (k : Fin D) :
    PiTensorProduct.map (oneOneProjector (K := K) e)
        (oneOnePure K P (e k)) = oneOnePure K D k := by
  unfold oneOnePure
  erw [PiTensorProduct.map_tprod]
  congr 1
  funext s
  fin_cases s
  · change (LinearMap.funLeft K K (fun ab : Fin 1 × Fin 1 ↦ ab))
        (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1) =
          (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 : Fin 1 × Fin 1 → K)
    exact funLeft_single_of_injective K
      (fun ab : Fin 1 × Fin 1 ↦ ab) Function.injective_id
      ((0 : Fin 1), (0 : Fin 1))
  · change (LinearMap.funLeft K K
        (fun ab : Fin 1 × Fin D ↦ (ab.1, e ab.2)))
        (Pi.single ((0 : Fin 1), e k) 1) =
          (Pi.single ((0 : Fin 1), k) 1 : Fin 1 × Fin D → K)
    exact funLeft_single_of_injective K
      (fun ab : Fin 1 × Fin D ↦ (ab.1, e ab.2))
      (by
        intro a b h
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · exact e.injective (congrArg Prod.snd h))
      ((0 : Fin 1), k)
  · change (LinearMap.funLeft K K
        (fun ab : Fin D × Fin 1 ↦ (e ab.1, ab.2)))
        (Pi.single (e k, (0 : Fin 1)) 1) =
          (Pi.single (k, (0 : Fin 1)) 1 : Fin D × Fin 1 → K)
    exact funLeft_single_of_injective K
      (fun ab : Fin D × Fin 1 ↦ (e ab.1, ab.2))
      (by
        intro a b h
        apply Prod.ext
        · exact e.injective (congrArg Prod.fst h)
        · exact Subsingleton.elim _ _)
      (k, (0 : Fin 1))

private theorem firstProjector_map_selected
    {K : Type u} [Field K] {D P : ℕ}
    (e : Fin D ↪ Fin P) (k : Fin D) :
    PiTensorProduct.map (firstProjector (K := K) e)
        (firstPure K P (e k)) = firstPure K D k := by
  unfold firstPure
  erw [PiTensorProduct.map_tprod]
  congr 1
  funext s
  fin_cases s
  · change (LinearMap.funLeft K K
        (fun ab : Fin D × Fin 1 ↦ (e ab.1, ab.2)))
        (Pi.single (e k, (0 : Fin 1)) 1) =
          (Pi.single (k, (0 : Fin 1)) 1 : Fin D × Fin 1 → K)
    exact funLeft_single_of_injective K
      (fun ab : Fin D × Fin 1 ↦ (e ab.1, ab.2))
      (by
        intro a b h
        apply Prod.ext
        · exact e.injective (congrArg Prod.fst h)
        · exact Subsingleton.elim _ _)
      (k, (0 : Fin 1))
  · change (LinearMap.funLeft K K (fun ab : Fin 1 × Fin 1 ↦ ab))
        (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1) =
          (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 : Fin 1 × Fin 1 → K)
    exact funLeft_single_of_injective K
      (fun ab : Fin 1 × Fin 1 ↦ ab) Function.injective_id
      ((0 : Fin 1), (0 : Fin 1))
  · change (LinearMap.funLeft K K
        (fun ab : Fin 1 × Fin D ↦ (ab.1, e ab.2)))
        (Pi.single ((0 : Fin 1), e k) 1) =
          (Pi.single ((0 : Fin 1), k) 1 : Fin 1 × Fin D → K)
    exact funLeft_single_of_injective K
      (fun ab : Fin 1 × Fin D ↦ (ab.1, e ab.2))
      (by
        intro a b h
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · exact e.injective (congrArg Prod.snd h))
      ((0 : Fin 1), k)

private theorem oneOneProjector_map_outside
    {K : Type u} [Field K] {D P : ℕ}
    (e : Fin D ↪ Fin P) (k' : Fin P)
    (hout : ∀ k : Fin D, e k ≠ k') :
    PiTensorProduct.map (oneOneProjector (K := K) e)
        (oneOnePure K P k') = 0 := by
  unfold oneOnePure
  erw [PiTensorProduct.map_tprod]
  apply (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3)
  exact funLeft_single_outside K
    (fun ab : Fin 1 × Fin D ↦ (ab.1, e ab.2))
    ((0 : Fin 1), k') (fun ab h ↦ hout ab.2 (congrArg Prod.snd h))

private theorem firstProjector_map_outside
    {K : Type u} [Field K] {D P : ℕ}
    (e : Fin D ↪ Fin P) (k' : Fin P)
    (hout : ∀ k : Fin D, e k ≠ k') :
    PiTensorProduct.map (firstProjector (K := K) e)
        (firstPure K P k') = 0 := by
  unfold firstPure
  erw [PiTensorProduct.map_tprod]
  apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
  exact funLeft_single_outside K
    (fun ab : Fin D × Fin 1 ↦ (e ab.1, ab.2))
    (k', (0 : Fin 1)) (fun ab h ↦ hout ab.1 (congrArg Prod.fst h))

private theorem oneOneProjector_maps_tensor
    {K : Type u} [Field K] {D P : ℕ} (e : Fin D ↪ Fin P) :
    PiTensorProduct.map (oneOneProjector (K := K) e)
        (MMObj K 1 1 P).t = (MMObj K 1 1 D).t := by
  rw [oneOneTensor_eq_sum_pure, oneOneTensor_eq_sum_pure]
  refine (map_sum (PiTensorProduct.map (oneOneProjector (K := K) e))
    (fun k : Fin P ↦ oneOnePure K P k) Finset.univ).trans ?_
  let range : Finset (Fin P) := Finset.univ.image e
  trans (∑ k : Fin D,
      PiTensorProduct.map (oneOneProjector (K := K) e) (oneOnePure K P (e k)))
  · calc
      (∑ k' : Fin P,
          PiTensorProduct.map (oneOneProjector (K := K) e)
            (oneOnePure K P k')) =
          ∑ k' ∈ range,
            PiTensorProduct.map (oneOneProjector (K := K) e)
              (oneOnePure K P k') := by
        symm
        apply Finset.sum_subset
        · simp [range]
        · intro k' _ hk'
          apply oneOneProjector_map_outside
          intro k hek
          apply hk'
          simp [range, ← hek]
      _ = ∑ k : Fin D,
            PiTensorProduct.map (oneOneProjector (K := K) e)
              (oneOnePure K P (e k)) := by
        simp only [range]
        exact Finset.sum_image e.injective.injOn
  · apply Finset.sum_congr rfl
    intro k _
    exact oneOneProjector_map_selected e k

private theorem firstProjector_maps_tensor
    {K : Type u} [Field K] {D P : ℕ} (e : Fin D ↪ Fin P) :
    PiTensorProduct.map (firstProjector (K := K) e)
        (MMObj K P 1 1).t = (MMObj K D 1 1).t := by
  rw [firstTensor_eq_sum_pure, firstTensor_eq_sum_pure]
  refine (map_sum (PiTensorProduct.map (firstProjector (K := K) e))
    (fun k : Fin P ↦ firstPure K P k) Finset.univ).trans ?_
  let range : Finset (Fin P) := Finset.univ.image e
  trans (∑ k : Fin D,
      PiTensorProduct.map (firstProjector (K := K) e) (firstPure K P (e k)))
  · calc
      (∑ k' : Fin P,
          PiTensorProduct.map (firstProjector (K := K) e)
            (firstPure K P k')) =
          ∑ k' ∈ range,
            PiTensorProduct.map (firstProjector (K := K) e)
              (firstPure K P k') := by
        symm
        apply Finset.sum_subset
        · simp [range]
        · intro k' _ hk'
          apply firstProjector_map_outside
          intro k hek
          apply hk'
          simp [range, ← hek]
      _ = ∑ k : Fin D,
            PiTensorProduct.map (firstProjector (K := K) e)
              (firstPure K P (e k)) := by
        simp only [range]
        exact Finset.sum_image e.injective.injOn
  · apply Finset.sum_congr rfl
    intro k _
    exact firstProjector_map_selected e k

/-! ## Generic exact-router descent -/

private def AllowedIndex {I : Type u} (allowed : I → Prop) :=
  {i : I // allowed i}

private noncomputable instance allowedIndexFintype
    {I : Type u} [Fintype I] (allowed : I → Prop) :
    Fintype (AllowedIndex allowed) := by
  unfold AllowedIndex
  letI : DecidablePred allowed := Classical.decPred _
  infer_instance

private noncomputable def allowedEquivFin
    {I : Type u} [Fintype I] (allowed : I → Prop) :
    AllowedIndex allowed ≃ Fin (Nat.card (AllowedIndex allowed)) :=
  (Fintype.equivFin _).trans (finCongr Nat.card_eq_fintype_card.symm)

private noncomputable def allowedEmbedding
    {I : Type u} [Fintype I] {P : ℕ}
    (allowed : I → Prop) (coord : I ↪ Fin P) :
    Fin (Nat.card (AllowedIndex allowed)) ↪ Fin P where
  toFun k := coord ((allowedEquivFin allowed).symm k).1
  inj' := by
    intro k l h
    apply (allowedEquivFin allowed).symm.injective
    apply Subtype.ext
    exact coord.injective h

private theorem allowedEmbedding_outside
    {I : Type u} [Fintype I] {P : ℕ}
    (allowed : I → Prop) (coord : I ↪ Fin P)
    (i : I) (hi : ¬ allowed i) :
    ∀ k, allowedEmbedding allowed coord k ≠ coord i := by
  intro k h
  apply hi
  have heq : ((allowedEquivFin allowed).symm k).1 = i :=
    coord.injective h
  exact heq ▸ ((allowedEquivFin allowed).symm k).2

/-- A basis-labelled exact router to `⟨1,1,P⟩` descends through any
literal Z-basis projection to `⟨1,1,D⟩`, where `D` is exactly the number of
selected source basis vectors.  This is the finite coordinate-selection step
needed for equal-multiplicity rectangular Table-2 rows. -/
theorem exactRouter_oneOne_allowedSubtensor_restrict
    {K : Type u} [Field K] {T : TensorObj K 3}
    {I : Type u} [Fintype I] [DecidableEq I]
    (bZ : Basis I K (T.V 2)) (allowed : I → Prop)
    [DecidablePred allowed] {P : ℕ} (coord : I ↪ Fin P)
    (router : ∀ s, T.V s →ₗ[K] (MMObj K 1 1 P).V s)
    (hrouter : PiTensorProduct.map router T.t = (MMObj K 1 1 P).t)
    (hrouterZ : ∀ i,
      router 2 (bZ i) =
        (Pi.single (coord i, (0 : Fin 1)) 1 : Fin P × Fin 1 → K)) :
    TensorObj.Restrict
      (MMObj K 1 1 (Nat.card {i : I // allowed i}))
      (T.basisZAllowedSubtensor bZ allowed) := by
  let e := allowedEmbedding allowed coord
  let f : ∀ s, T.V s →ₗ[K]
      (MMObj K 1 1 (Nat.card (AllowedIndex allowed))).V s := fun s ↦
    (oneOneProjector (K := K) e s).comp (router s)
  have hmap : PiTensorProduct.map f T.t =
      (MMObj K 1 1 (Nat.card (AllowedIndex allowed))).t := by
    change PiTensorProduct.map
        (fun s ↦ (oneOneProjector (K := K) e s) ∘ₗ router s) T.t = _
    rw [PiTensorProduct.map_comp]
    simp only [LinearMap.comp_apply]
    rw [hrouter, oneOneProjector_maps_tensor]
  have hvanish : ∀ i, ¬ allowed i → f 2 (bZ i) = 0 := by
    intro i hi
    simp only [f, LinearMap.comp_apply, hrouterZ]
    exact funLeft_single_outside K
      (fun ab : Fin (Nat.card (AllowedIndex allowed)) × Fin 1 ↦
        (e ab.1, ab.2))
      (coord i, (0 : Fin 1))
      (fun ab h ↦ allowedEmbedding_outside allowed coord i hi ab.1
        (congrArg Prod.fst h))
  exact mme_restrict_basisZAllowedSubtensor_of_vanishes
    T (MMObj K 1 1 (Nat.card (AllowedIndex allowed)))
      bZ allowed f hmap hvanish

/-- The mode-rotated companion for exact routers to `⟨P,1,1⟩`. -/
theorem exactRouter_first_allowedSubtensor_restrict
    {K : Type u} [Field K] {T : TensorObj K 3}
    {I : Type u} [Fintype I] [DecidableEq I]
    (bZ : Basis I K (T.V 2)) (allowed : I → Prop)
    [DecidablePred allowed] {P : ℕ} (coord : I ↪ Fin P)
    (router : ∀ s, T.V s →ₗ[K] (MMObj K P 1 1).V s)
    (hrouter : PiTensorProduct.map router T.t = (MMObj K P 1 1).t)
    (hrouterZ : ∀ i,
      router 2 (bZ i) =
        (Pi.single ((0 : Fin 1), coord i) 1 : Fin 1 × Fin P → K)) :
    TensorObj.Restrict
      (MMObj K (Nat.card {i : I // allowed i}) 1 1)
      (T.basisZAllowedSubtensor bZ allowed) := by
  let e := allowedEmbedding allowed coord
  let f : ∀ s, T.V s →ₗ[K]
      (MMObj K (Nat.card (AllowedIndex allowed)) 1 1).V s := fun s ↦
    (firstProjector (K := K) e s).comp (router s)
  have hmap : PiTensorProduct.map f T.t =
      (MMObj K (Nat.card (AllowedIndex allowed)) 1 1).t := by
    change PiTensorProduct.map
        (fun s ↦ (firstProjector (K := K) e s) ∘ₗ router s) T.t = _
    rw [PiTensorProduct.map_comp]
    simp only [LinearMap.comp_apply]
    rw [hrouter, firstProjector_maps_tensor]
  have hvanish : ∀ i, ¬ allowed i → f 2 (bZ i) = 0 := by
    intro i hi
    simp only [f, LinearMap.comp_apply, hrouterZ]
    exact funLeft_single_outside K
      (fun ab : Fin 1 × Fin (Nat.card (AllowedIndex allowed)) ↦
        (ab.1, e ab.2))
      ((0 : Fin 1), coord i)
      (fun ab h ↦ allowedEmbedding_outside allowed coord i hi ab.2
        (congrArg Prod.snd h))
  exact mme_restrict_basisZAllowedSubtensor_of_vanishes
    T (MMObj K (Nat.card (AllowedIndex allowed)) 1 1)
      bZ allowed f hmap hvanish

end MME.DWZBalancedRectangular

/-- Submission wrapper for the first rectangular orientation. -/
theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3}
    {I : Type u} [Fintype I] [DecidableEq I]
    (bZ : Basis I K (T.V 2)) (allowed : I → Prop)
    [DecidablePred allowed] {P : ℕ} (coord : I ↪ Fin P)
    (router : ∀ s, T.V s →ₗ[K] (MMObj K 1 1 P).V s)
    (hrouter : PiTensorProduct.map router T.t = (MMObj K 1 1 P).t)
    (hrouterZ : ∀ i,
      router 2 (bZ i) =
        (Pi.single (coord i, (0 : Fin 1)) 1 : Fin P × Fin 1 → K)) :
    TensorObj.Restrict
      (MMObj K 1 1 (Nat.card {i : I // allowed i}))
      (T.basisZAllowedSubtensor bZ allowed) := by
  exact MME.DWZBalancedRectangular.exactRouter_oneOne_allowedSubtensor_restrict
    bZ allowed coord router hrouter hrouterZ
