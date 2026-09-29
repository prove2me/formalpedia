-- Prove2me | solution 1 for mme_CW_q6_exact_address_central_cell_union_balanced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T11:17:40.285464+00:00
-- url     : https://prove2.me/submissions/2ecc84dd-2b9e-4d5f-899c-e62e4cc7deed

import Mathlib.Tactic
import Theorems.Thm_mme_CW_q6_exact_address_joint_xy_counts

open MME

set_option autoImplicit false
set_option warningAsError true

/-- Selecting the central number of coordinates from each of the four joint
X/Y cells produces one balanced half. -/
theorem solution
    {n L G : ℕ} (hLG : L + G = 2 * n)
    (address : CWQ6ExactCoupledAddress (2 * n) L G)
    (S00 S11 S01 S10 : Finset (Fin (2 * (2 * n))))
    (h00 : S00 ⊆ (Finset.univ.filter
      (fun j ↦ address.1 0 j = 0 ∧ address.1 1 j = 0)))
    (h11 : S11 ⊆ (Finset.univ.filter
      (fun j ↦ address.1 0 j = 1 ∧ address.1 1 j = 1)))
    (h01 : S01 ⊆ (Finset.univ.filter
      (fun j ↦ address.1 0 j = 0 ∧ address.1 1 j = 1)))
    (h10 : S10 ⊆ (Finset.univ.filter
      (fun j ↦ address.1 0 j = 1 ∧ address.1 1 j = 0)))
    (hc00 : S00.card = L / 2) (hc11 : S11.card = L / 2)
    (hc01 : S01.card = n - L / 2) (hc10 : S10.card = n - L / 2) :
    let S := S00 ∪ S11 ∪ S01 ∪ S10
    S.card = 2 * n ∧
      (∀ grade : Fin 3,
        (S.filter (fun j ↦ address.1 0 j = grade)).card =
          if grade = 0 then n else if grade = 1 then n else 0) ∧
      (∀ grade : Fin 3,
        ((Finset.univ \ S).filter
          (fun j ↦ address.1 1 j = grade)).card =
          if grade = 0 then n else if grade = 1 then n else 0) := by
  classical
  let S := S00 ∪ S11 ∪ S01 ∪ S10
  have ht : L / 2 ≤ n := by omega
  have htu : L / 2 + (n - L / 2) = n := by omega
  have hx00 (j) (hj : j ∈ S00) :
      address.1 0 j = 0 ∧ address.1 1 j = 0 :=
    (Finset.mem_filter.mp (h00 hj)).2
  have hx11 (j) (hj : j ∈ S11) :
      address.1 0 j = 1 ∧ address.1 1 j = 1 :=
    (Finset.mem_filter.mp (h11 hj)).2
  have hx01 (j) (hj : j ∈ S01) :
      address.1 0 j = 0 ∧ address.1 1 j = 1 :=
    (Finset.mem_filter.mp (h01 hj)).2
  have hx10 (j) (hj : j ∈ S10) :
      address.1 0 j = 1 ∧ address.1 1 j = 0 :=
    (Finset.mem_filter.mp (h10 hj)).2
  have hd0011 : Disjoint S00 S11 := Finset.disjoint_left.mpr (by
    intro j hj00 hj11
    have := hx00 j hj00
    have := hx11 j hj11
    omega)
  have hd0001 : Disjoint S00 S01 := Finset.disjoint_left.mpr (by
    intro j hj00 hj01
    have := hx00 j hj00
    have := hx01 j hj01
    omega)
  have hd0010 : Disjoint S00 S10 := Finset.disjoint_left.mpr (by
    intro j hj00 hj10
    have := hx00 j hj00
    have := hx10 j hj10
    omega)
  have hd1101 : Disjoint S11 S01 := Finset.disjoint_left.mpr (by
    intro j hj11 hj01
    have := hx11 j hj11
    have := hx01 j hj01
    omega)
  have hd1110 : Disjoint S11 S10 := Finset.disjoint_left.mpr (by
    intro j hj11 hj10
    have := hx11 j hj11
    have := hx10 j hj10
    omega)
  have hd0110 : Disjoint S01 S10 := Finset.disjoint_left.mpr (by
    intro j hj01 hj10
    have := hx01 j hj01
    have := hx10 j hj10
    omega)
  have hcardS : S.card = 2 * n := by
    dsimp [S]
    rw [Finset.card_union_of_disjoint]
    · rw [Finset.card_union_of_disjoint]
      · rw [Finset.card_union_of_disjoint hd0011]
        omega
      · exact Finset.disjoint_union_left.mpr ⟨hd0001, hd1101⟩
    · exact Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_left.mpr ⟨hd0010, hd1110⟩, hd0110⟩
  refine ⟨hcardS, ?_, ?_⟩
  · intro grade
    fin_cases grade
    · have heq : S.filter (fun j ↦ address.1 0 j = 0) = S00 ∪ S01 := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_union, S]
        constructor
        · rintro ⟨(((hj00 | hj11) | hj01) | hj10), hx⟩
          · exact Or.inl hj00
          · exfalso
            have h := (hx11 j hj11).1
            omega
          · exact Or.inr hj01
          · exfalso
            have h := (hx10 j hj10).1
            omega
        · rintro (hj00 | hj01)
          · exact ⟨Or.inl (Or.inl (Or.inl hj00)), (hx00 j hj00).1⟩
          · exact ⟨Or.inl (Or.inr hj01), (hx01 j hj01).1⟩
      have hcard :
          (S.filter (fun j ↦ address.1 0 j = (0 : Fin 3))).card = n := by
        rw [heq, Finset.card_union_of_disjoint hd0001, hc00, hc01]
        omega
      simpa only [S, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceEq, reduceIte] using hcard
    · have heq : S.filter (fun j ↦ address.1 0 j = 1) = S11 ∪ S10 := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_union, S]
        constructor
        · rintro ⟨(((hj00 | hj11) | hj01) | hj10), hx⟩
          · exfalso
            have h := (hx00 j hj00).1
            omega
          · exact Or.inl hj11
          · exfalso
            have h := (hx01 j hj01).1
            omega
          · exact Or.inr hj10
        · rintro (hj11 | hj10)
          · exact ⟨Or.inl (Or.inl (Or.inr hj11)), (hx11 j hj11).1⟩
          · exact ⟨Or.inr hj10, (hx10 j hj10).1⟩
      have hcard :
          (S.filter (fun j ↦ address.1 0 j = (1 : Fin 3))).card = n := by
        rw [heq, Finset.card_union_of_disjoint hd1110, hc11, hc10]
        omega
      simpa only [S, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceEq, reduceIte] using hcard
    · have heq :
          S.filter (fun j ↦ address.1 0 j = (2 : Fin 3)) = ∅ := by
        apply Finset.Subset.antisymm
        · intro j hj
          have hx := (Finset.mem_filter.mp hj).2
          have hjS := (Finset.mem_filter.mp hj).1
          simp only [S, Finset.mem_union] at hjS
          rcases hjS with (((hj00 | hj11) | hj01) | hj10)
          · exfalso
            have h := (hx00 j hj00).1
            omega
          · exfalso
            have h := (hx11 j hj11).1
            omega
          · exfalso
            have h := (hx01 j hj01).1
            omega
          · exfalso
            have h := (hx10 j hj10).1
            omega
        · exact Finset.empty_subset _
      have hcard :
          (S.filter (fun j ↦ address.1 0 j = (2 : Fin 3))).card = 0 := by
        rw [heq]
        rfl
      have hmk2 : (⟨2, by omega⟩ : Fin 3) = 2 := rfl
      simpa only [S, hmk2, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceEq, reduceIte] using hcard
  · intro grade
    fin_cases grade
    · have hsel : S.filter (fun j ↦ address.1 1 j = 0) = S00 ∪ S10 := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_union, S]
        constructor
        · rintro ⟨(((hj00 | hj11) | hj01) | hj10), hy⟩
          · exact Or.inl hj00
          · exfalso
            have h := (hx11 j hj11).2
            omega
          · exfalso
            have h := (hx01 j hj01).2
            omega
          · exact Or.inr hj10
        · rintro (hj00 | hj10)
          · exact ⟨Or.inl (Or.inl (Or.inl hj00)), (hx00 j hj00).2⟩
          · exact ⟨Or.inr hj10, (hx10 j hj10).2⟩
      have hselcard :
          (S.filter (fun j ↦ address.1 1 j = (0 : Fin 3))).card = n := by
        rw [hsel, Finset.card_union_of_disjoint hd0010, hc00, hc10]
        omega
      have hglobal :
          (Finset.univ.filter
            (fun j ↦ address.1 1 j = (0 : Fin 3))).card = 2 * n := by
        simpa [cwQ6CoupledMarginalMultiplicity] using
          address.2.2 (1 : Fin 3) (0 : Fin 3)
      have heq :
          ((Finset.univ \ S).filter
            (fun j ↦ address.1 1 j = (0 : Fin 3))) =
          (Finset.univ.filter
            (fun j ↦ address.1 1 j = (0 : Fin 3))) \
            (S.filter (fun j ↦ address.1 1 j = (0 : Fin 3))) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
          true_and]
        tauto
      have hsub :
          S.filter (fun j ↦ address.1 1 j = (0 : Fin 3)) ⊆
            Finset.univ.filter
              (fun j ↦ address.1 1 j = (0 : Fin 3)) := by
        intro j hj
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
      have hcard :
          ((Finset.univ \ S).filter
            (fun j ↦ address.1 1 j = (0 : Fin 3))).card = n := by
        rw [heq, Finset.card_sdiff]
        rw [Finset.inter_eq_left.mpr hsub, hglobal, hselcard]
        omega
      simpa only [S, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceEq, reduceIte] using hcard
    · have hsel : S.filter (fun j ↦ address.1 1 j = 1) = S11 ∪ S01 := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_union, S]
        constructor
        · rintro ⟨(((hj00 | hj11) | hj01) | hj10), hy⟩
          · exfalso
            have h := (hx00 j hj00).2
            omega
          · exact Or.inl hj11
          · exact Or.inr hj01
          · exfalso
            have h := (hx10 j hj10).2
            omega
        · rintro (hj11 | hj01)
          · exact ⟨Or.inl (Or.inl (Or.inr hj11)), (hx11 j hj11).2⟩
          · exact ⟨Or.inl (Or.inr hj01), (hx01 j hj01).2⟩
      have hselcard :
          (S.filter (fun j ↦ address.1 1 j = (1 : Fin 3))).card = n := by
        rw [hsel, Finset.card_union_of_disjoint hd1101, hc11, hc01]
        omega
      have hglobal :
          (Finset.univ.filter
            (fun j ↦ address.1 1 j = (1 : Fin 3))).card = 2 * n := by
        simpa [cwQ6CoupledMarginalMultiplicity] using
          address.2.2 (1 : Fin 3) (1 : Fin 3)
      have heq :
          ((Finset.univ \ S).filter
            (fun j ↦ address.1 1 j = (1 : Fin 3))) =
          (Finset.univ.filter
            (fun j ↦ address.1 1 j = (1 : Fin 3))) \
            (S.filter (fun j ↦ address.1 1 j = (1 : Fin 3))) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
          true_and]
        tauto
      have hsub :
          S.filter (fun j ↦ address.1 1 j = (1 : Fin 3)) ⊆
            Finset.univ.filter
              (fun j ↦ address.1 1 j = (1 : Fin 3)) := by
        intro j hj
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
      have hcard :
          ((Finset.univ \ S).filter
            (fun j ↦ address.1 1 j = (1 : Fin 3))).card = n := by
        rw [heq, Finset.card_sdiff]
        rw [Finset.inter_eq_left.mpr hsub, hglobal, hselcard]
        omega
      simpa only [S, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceEq, reduceIte] using hcard
    · have hglobal :
          (Finset.univ.filter
            (fun j ↦ address.1 1 j = (2 : Fin 3))).card = 0 := by
        simpa [cwQ6CoupledMarginalMultiplicity] using
          address.2.2 (1 : Fin 3) (2 : Fin 3)
      have hempty :
          Finset.univ.filter
            (fun j ↦ address.1 1 j = (2 : Fin 3)) = ∅ :=
        Finset.card_eq_zero.mp hglobal
      have hsub :
          (Finset.univ \ S).filter
              (fun j ↦ address.1 1 j = (2 : Fin 3)) ⊆
            Finset.univ.filter
              (fun j ↦ address.1 1 j = (2 : Fin 3)) := by
        intro j hj
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
      have heq :
          (Finset.univ \ S).filter
              (fun j ↦ address.1 1 j = (2 : Fin 3)) = ∅ := by
        rw [← Finset.subset_empty]
        simpa [hempty] using hsub
      have hcard :
          ((Finset.univ \ S).filter
            (fun j ↦ address.1 1 j = (2 : Fin 3))).card = 0 := by
        rw [heq]
        rfl
      have hmk2 : (⟨2, by omega⟩ : Fin 3) = 2 := rfl
      simpa only [S, hmk2, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceEq, reduceIte] using hcard
