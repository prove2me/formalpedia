-- Prove2me | solution 1 for mme_dwz_table2_fixed_small_compatible_outer_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T18:43:31.792739+00:00
-- url     : https://prove2.me/submissions/2d0907cb-10f8-4db9-b1ec-1197a4337008

import Definitions.Def_mme_dwz_table2_split_assignments
import Definitions.Def_mme_dwz_table2_pair_coarsening

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZFixedSmallCandidates

private def regionOfShape :
    Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
  if h : MME.DWZSquare.shapeX s = 0 ∨
      MME.DWZSquare.shapeY s = 0 then
    Sum.inl ⟨s, h⟩
  else
    Sum.inr (MME.DWZSquare.shapeZ s)

private abbrev Outer
    (m : ℕ) {Position : Type*} [Fintype Position]
    (K : Position → Fin 5) :=
  {w : Position → Fin 15 //
    (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
    ∀ s, Fintype.card {t : Position // w t = s} =
      MME.DWZTable2Counts.component s * m}

private abbrev Typical
    (m : ℕ) {Position : Type*} [Fintype Position]
    (K : Position → Fin 5) :=
  {small : Position → Fin 3 × Fin 3 //
    (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
    ∀ p, Fintype.card {t : Position // small t = p} =
      MME.DWZTable2Counts.gamma p * m}

private def Compatible
    (m : ℕ) {Position : Type*} [Fintype Position]
    (K : Position → Fin 5)
    (I : Outer m K) (small : Typical m K) : Prop :=
  ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
    Fintype.card
        {t : Position //
          regionOfShape (I.1 t) = r ∧ (small.1 t).1 = a} =
      MME.DWZTable2Cardinality.cellCount m r a

private noncomputable def positionEquiv
    (m : ℕ) {Position : Type*} [Fintype Position]
    (K : Position → Fin 5)
    (small₁ small₂ : Typical m K) : Position ≃ Position :=
  Equiv.ofFiberEquiv (f := small₁.1) (g := small₂.1) fun p ↦
    Fintype.equivOfCardEq (by rw [small₁.2.2 p, small₂.2.2 p])

private theorem positionEquiv_maps
    (m : ℕ) {Position : Type*} [Fintype Position]
    (K : Position → Fin 5)
    (small₁ small₂ : Typical m K) (t : Position) :
    small₂.1 (positionEquiv m K small₁ small₂ t) = small₁.1 t := by
  exact Equiv.ofFiberEquiv_map
    (fun p ↦ Fintype.equivOfCardEq (by
      rw [small₁.2.2 p, small₂.2.2 p])) t

private theorem positionEquiv_preserves_K
    (m : ℕ) {Position : Type*} [Fintype Position]
    (K : Position → Fin 5)
    (small₁ small₂ : Typical m K) (t : Position) :
    K (positionEquiv m K small₁ small₂ t) = K t := by
  calc
    K (positionEquiv m K small₁ small₂ t) =
        MME.DWZTable2Counts.coarseOf
          (small₂.1 (positionEquiv m K small₁ small₂ t)) :=
      (small₂.2.1 _).symm
    _ = MME.DWZTable2Counts.coarseOf (small₁.1 t) :=
      congrArg MME.DWZTable2Counts.coarseOf
        (positionEquiv_maps m K small₁ small₂ t)
    _ = K t := small₁.2.1 t

private noncomputable def reindexOuter
    (m : ℕ) {Position : Type*} [Fintype Position]
    (K : Position → Fin 5)
    (small₁ small₂ : Typical m K) : Outer m K ≃ Outer m K := by
  classical
  let e := positionEquiv m K small₁ small₂
  let forward : Outer m K → Outer m K := fun I ↦ ⟨
    fun t ↦ I.1 (e.symm t),
    ⟨fun t ↦ by
      calc
        MME.DWZSquare.shapeZ (I.1 (e.symm t)) = K (e.symm t) :=
          I.2.1 (e.symm t)
        _ = K t := (positionEquiv_preserves_K
          m K small₁ small₂ (e.symm t)).symm.trans (by simp [e]),
      fun s ↦ by
        let fiberEquiv :
            {u : Position // I.1 u = s} ≃
              {t : Position // I.1 (e.symm t) = s} :=
          Equiv.subtypeEquiv e (fun u ↦ by simp)
        rw [← Fintype.card_congr fiberEquiv]
        exact I.2.2 s⟩⟩
  let backward : Outer m K → Outer m K := fun I ↦ ⟨
    fun t ↦ I.1 (e t),
    ⟨fun t ↦ by
      calc
        MME.DWZSquare.shapeZ (I.1 (e t)) = K (e t) := I.2.1 (e t)
        _ = K t := positionEquiv_preserves_K m K small₁ small₂ t,
      fun s ↦ by
        let fiberEquiv :
            {u : Position // I.1 u = s} ≃
              {t : Position // I.1 (e t) = s} :=
          Equiv.subtypeEquiv e.symm (fun u ↦ by simp)
        rw [← Fintype.card_congr fiberEquiv]
        exact I.2.2 s⟩⟩
  exact
    { toFun := forward
      invFun := backward
      left_inv := by
        intro I
        apply Subtype.ext
        funext t
        simp [forward, backward, e]
      right_inv := by
        intro I
        apply Subtype.ext
        funext t
        simp [forward, backward, e] }

@[simp] private theorem reindexOuter_apply
    (m : ℕ) {Position : Type*} [Fintype Position]
    (K : Position → Fin 5)
    (small₁ small₂ : Typical m K) (I : Outer m K) (t : Position) :
    (reindexOuter m K small₁ small₂ I).1 t =
      I.1 ((positionEquiv m K small₁ small₂).symm t) := by
  rfl

private theorem reindexOuter_compatible
    (m : ℕ) {Position : Type*} [Fintype Position] [DecidableEq Position]
    (K : Position → Fin 5)
    (small₁ small₂ : Typical m K) (I : Outer m K) :
    Compatible m K I small₁ ↔
      Compatible m K (reindexOuter m K small₁ small₂ I) small₂ := by
  classical
  let e := positionEquiv m K small₁ small₂
  constructor <;> intro h r a
  · let fiberEquiv :
        {u : Position //
          regionOfShape (I.1 u) = r ∧ (small₁.1 u).1 = a} ≃
        {t : Position //
          regionOfShape
              ((reindexOuter m K small₁ small₂ I).1 t) = r ∧
            (small₂.1 t).1 = a} :=
      Equiv.subtypeEquiv e (fun u ↦ by
        simp only [reindexOuter_apply, e, Equiv.symm_apply_apply,
          positionEquiv_maps])
    rw [← Fintype.card_congr fiberEquiv]
    exact h r a
  · let fiberEquiv :
        {t : Position //
          regionOfShape
              ((reindexOuter m K small₁ small₂ I).1 t) = r ∧
            (small₂.1 t).1 = a} ≃
        {u : Position //
          regionOfShape (I.1 u) = r ∧ (small₁.1 u).1 = a} :=
      Equiv.subtypeEquiv e.symm (fun t ↦ by
        have hmap := positionEquiv_maps m K small₁ small₂ (e.symm t)
        simp only [e, Equiv.apply_symm_apply] at hmap
        simp only [reindexOuter_apply, e]
        rw [hmap])
    rw [← Fintype.card_congr fiberEquiv]
    exact h r a

private noncomputable def compatibleOuterEquiv
    (m : ℕ) {Position : Type*} [Fintype Position] [DecidableEq Position]
    (K : Position → Fin 5)
    (small₁ small₂ : Typical m K) :
    {I : Outer m K // Compatible m K I small₁} ≃
      {I : Outer m K // Compatible m K I small₂} :=
  Equiv.subtypeEquiv (reindexOuter m K small₁ small₂)
    (reindexOuter_compatible m K small₁ small₂)

end MME.DWZFixedSmallCandidates

open MME.DWZFixedSmallCandidates

theorem solution
    (m : ℕ)
    {Position : Type*} [Fintype Position] [DecidableEq Position]
    (K : Position → Fin 5) :
    let regionOfShape :
        Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
      if h : MME.DWZSquare.shapeX s = 0 ∨
          MME.DWZSquare.shapeY s = 0 then
        Sum.inl ⟨s, h⟩
      else
        Sum.inr (MME.DWZSquare.shapeZ s)
    let Outer :=
      {w : Position → Fin 15 //
        (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
        ∀ s, Fintype.card {t : Position // w t = s} =
          MME.DWZTable2Counts.component s * m}
    let Typical :=
      {small : Position → Fin 3 × Fin 3 //
        (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
        ∀ p, Fintype.card {t : Position // small t = p} =
          MME.DWZTable2Counts.gamma p * m}
    let Compatible : Outer → Typical → Prop := fun I small ↦
      ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
        Fintype.card
            {t : Position //
              regionOfShape (I.1 t) = r ∧ (small.1 t).1 = a} =
          MME.DWZTable2Cardinality.cellCount m r a
    ∀ small₁ small₂ : Typical,
      Nat.card {I : Outer // Compatible I small₁} =
        Nat.card {I : Outer // Compatible I small₂} := by
  classical
  change ∀ small₁ small₂ : Typical m K,
    Nat.card {I : Outer m K // Compatible m K I small₁} =
      Nat.card {I : Outer m K // Compatible m K I small₂}
  intro small₁ small₂
  exact Nat.card_congr (compatibleOuterEquiv m K small₁ small₂)
