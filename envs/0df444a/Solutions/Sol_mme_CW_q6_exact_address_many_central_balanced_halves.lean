-- Prove2me | solution 1 for mme_CW_q6_exact_address_many_central_balanced_halves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T11:31:15.300132+00:00
-- url     : https://prove2.me/submissions/b2f581e9-ff98-4273-9a46-9e5ffe462a0d

import Mathlib.Tactic
import Theorems.Thm_mme_CW_q6_exact_address_central_cell_union_balanced
import Theorems.Thm_mme_CW_q6_exact_address_joint_xy_counts

open MME

set_option autoImplicit false
set_option warningAsError true

/-- Every exact coupled address admits the full product family of central
four-cell balanced halves. -/
theorem solution
    {n L G : ℕ} (hLG : L + G = 2 * n)
    (address : CWQ6ExactCoupledAddress (2 * n) L G) :
    ∃ halves : Finset (Finset (Fin (2 * (2 * n)))),
      halves.card =
        (Nat.choose L (L / 2) * Nat.choose L (L / 2)) *
          (Nat.choose G (n - L / 2) * Nat.choose G (n - L / 2)) ∧
      ∀ S ∈ halves,
        S.card = 2 * n ∧
          (∀ grade : Fin 3,
            (S.filter (fun j ↦ address.1 0 j = grade)).card =
              if grade = 0 then n else if grade = 1 then n else 0) ∧
          (∀ grade : Fin 3,
            ((Finset.univ \ S).filter
              (fun j ↦ address.1 1 j = grade)).card =
              if grade = 0 then n else if grade = 1 then n else 0) := by
  classical
  let C00 := (Finset.univ : Finset (Fin (2 * (2 * n)))).filter
    (fun j ↦ address.1 0 j = 0 ∧ address.1 1 j = 0)
  let C11 := (Finset.univ : Finset (Fin (2 * (2 * n)))).filter
    (fun j ↦ address.1 0 j = 1 ∧ address.1 1 j = 1)
  let C01 := (Finset.univ : Finset (Fin (2 * (2 * n)))).filter
    (fun j ↦ address.1 0 j = 0 ∧ address.1 1 j = 1)
  let C10 := (Finset.univ : Finset (Fin (2 * (2 * n)))).filter
    (fun j ↦ address.1 0 j = 1 ∧ address.1 1 j = 0)
  have hcounts := mme_CW_q6_exact_address_joint_xy_counts
    (N := 2 * n) hLG address
  have hc00 : C00.card = L := hcounts.1
  have hc11 : C11.card = L := hcounts.2.1
  have hc01 : C01.card = G := hcounts.2.2.1
  have hc10 : C10.card = G := hcounts.2.2.2
  have hGchoice : n - L / 2 ≤ G := by omega
  let choices :=
    ((C00.powersetCard (L / 2)).product
      (C11.powersetCard (L / 2))).product
    ((C01.powersetCard (n - L / 2)).product
      (C10.powersetCard (n - L / 2)))
  let join :
      ((Finset (Fin (2 * (2 * n))) × Finset (Fin (2 * (2 * n)))) ×
        (Finset (Fin (2 * (2 * n))) × Finset (Fin (2 * (2 * n))))) →
        Finset (Fin (2 * (2 * n))) :=
    fun q ↦ q.1.1 ∪ q.1.2 ∪ q.2.1 ∪ q.2.2
  let halves := choices.image join
  have hdisj (a b c d : Fin 3) (hab : (a, b) ≠ (c, d)) :
      Disjoint
        ((Finset.univ : Finset (Fin (2 * (2 * n)))).filter
          (fun j ↦ address.1 0 j = a ∧ address.1 1 j = b))
        ((Finset.univ : Finset (Fin (2 * (2 * n)))).filter
          (fun j ↦ address.1 0 j = c ∧ address.1 1 j = d)) := by
    rw [Finset.disjoint_left]
    intro j hj hk
    simp only [Finset.mem_filter] at hj hk
    apply hab
    exact Prod.ext (hj.2.1.symm.trans hk.2.1)
      (hj.2.2.symm.trans hk.2.2)
  have hd0011 : Disjoint C00 C11 := hdisj 0 0 1 1 (by decide)
  have hd0001 : Disjoint C00 C01 := hdisj 0 0 0 1 (by decide)
  have hd0010 : Disjoint C00 C10 := hdisj 0 0 1 0 (by decide)
  have hd1101 : Disjoint C11 C01 := hdisj 1 1 0 1 (by decide)
  have hd1110 : Disjoint C11 C10 := hdisj 1 1 1 0 (by decide)
  have hd0110 : Disjoint C01 C10 := hdisj 0 1 1 0 (by decide)
  have hrecover
      (A B C D X : Finset (Fin (2 * (2 * n))))
      (hA : A ⊆ X) (hB : Disjoint B X)
      (hC : Disjoint C X) (hD : Disjoint D X) :
      (A ∪ B ∪ C ∪ D) ∩ X = A := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨(((hjA | hjB) | hjC) | hjD), hjX⟩
      · exact hjA
      · exact (Finset.disjoint_left.mp hB hjB hjX).elim
      · exact (Finset.disjoint_left.mp hC hjC hjX).elim
      · exact (Finset.disjoint_left.mp hD hjD hjX).elim
    · intro hjA
      exact ⟨Or.inl (Or.inl (Or.inl hjA)), hA hjA⟩
  have hinj : Set.InjOn join choices := by
    intro q hq r hr heq
    rcases Finset.mem_product.mp hq with ⟨hqL, hqR⟩
    rcases Finset.mem_product.mp hqL with ⟨hq00m, hq11m⟩
    rcases Finset.mem_product.mp hqR with ⟨hq01m, hq10m⟩
    rcases Finset.mem_product.mp hr with ⟨hrL, hrR⟩
    rcases Finset.mem_product.mp hrL with ⟨hr00m, hr11m⟩
    rcases Finset.mem_product.mp hrR with ⟨hr01m, hr10m⟩
    have hq00 := (Finset.mem_powersetCard.mp hq00m).1
    have hq11 := (Finset.mem_powersetCard.mp hq11m).1
    have hq01 := (Finset.mem_powersetCard.mp hq01m).1
    have hq10 := (Finset.mem_powersetCard.mp hq10m).1
    have hr00 := (Finset.mem_powersetCard.mp hr00m).1
    have hr11 := (Finset.mem_powersetCard.mp hr11m).1
    have hr01 := (Finset.mem_powersetCard.mp hr01m).1
    have hr10 := (Finset.mem_powersetCard.mp hr10m).1
    have eq00 : q.1.1 = r.1.1 := by
      calc
        q.1.1 = join q ∩ C00 :=
          (hrecover q.1.1 q.1.2 q.2.1 q.2.2 C00 hq00
            (hd0011.symm.mono hq11 Finset.Subset.rfl)
            (hd0001.symm.mono hq01 Finset.Subset.rfl)
            (hd0010.symm.mono hq10 Finset.Subset.rfl)).symm
        _ = join r ∩ C00 := by rw [heq]
        _ = r.1.1 :=
          hrecover r.1.1 r.1.2 r.2.1 r.2.2 C00 hr00
            (hd0011.symm.mono hr11 Finset.Subset.rfl)
            (hd0001.symm.mono hr01 Finset.Subset.rfl)
            (hd0010.symm.mono hr10 Finset.Subset.rfl)
    have eq11 : q.1.2 = r.1.2 := by
      calc
        q.1.2 = join q ∩ C11 :=
          (by simpa [join, Finset.union_comm, Finset.union_left_comm,
              Finset.union_assoc] using
            (hrecover q.1.2 q.1.1 q.2.1 q.2.2 C11 hq11
              (hd0011.mono hq00 Finset.Subset.rfl)
              (hd1101.symm.mono hq01 Finset.Subset.rfl)
              (hd1110.symm.mono hq10 Finset.Subset.rfl)).symm)
        _ = join r ∩ C11 := by rw [heq]
        _ = r.1.2 :=
          (by simpa [join, Finset.union_comm, Finset.union_left_comm,
              Finset.union_assoc] using
            (hrecover r.1.2 r.1.1 r.2.1 r.2.2 C11 hr11
              (hd0011.mono hr00 Finset.Subset.rfl)
              (hd1101.symm.mono hr01 Finset.Subset.rfl)
              (hd1110.symm.mono hr10 Finset.Subset.rfl)))
    have eq01 : q.2.1 = r.2.1 := by
      calc
        q.2.1 = join q ∩ C01 :=
          (by simpa [join, Finset.union_comm, Finset.union_left_comm,
              Finset.union_assoc] using
            (hrecover q.2.1 q.1.1 q.1.2 q.2.2 C01 hq01
              (hd0001.mono hq00 Finset.Subset.rfl)
              (hd1101.mono hq11 Finset.Subset.rfl)
              (hd0110.symm.mono hq10 Finset.Subset.rfl)).symm)
        _ = join r ∩ C01 := by rw [heq]
        _ = r.2.1 :=
          (by simpa [join, Finset.union_comm, Finset.union_left_comm,
              Finset.union_assoc] using
            (hrecover r.2.1 r.1.1 r.1.2 r.2.2 C01 hr01
              (hd0001.mono hr00 Finset.Subset.rfl)
              (hd1101.mono hr11 Finset.Subset.rfl)
              (hd0110.symm.mono hr10 Finset.Subset.rfl)))
    have eq10 : q.2.2 = r.2.2 := by
      calc
        q.2.2 = join q ∩ C10 :=
          (by simpa [join, Finset.union_comm, Finset.union_left_comm,
              Finset.union_assoc] using
            (hrecover q.2.2 q.1.1 q.1.2 q.2.1 C10 hq10
              (hd0010.mono hq00 Finset.Subset.rfl)
              (hd1110.mono hq11 Finset.Subset.rfl)
              (hd0110.mono hq01 Finset.Subset.rfl)).symm)
        _ = join r ∩ C10 := by rw [heq]
        _ = r.2.2 :=
          (by simpa [join, Finset.union_comm, Finset.union_left_comm,
              Finset.union_assoc] using
            (hrecover r.2.2 r.1.1 r.1.2 r.2.1 C10 hr10
              (hd0010.mono hr00 Finset.Subset.rfl)
              (hd1110.mono hr11 Finset.Subset.rfl)
              (hd0110.mono hr01 Finset.Subset.rfl)))
    exact Prod.ext (Prod.ext eq00 eq11) (Prod.ext eq01 eq10)
  refine ⟨halves, ?_, ?_⟩
  · rw [show halves = choices.image join by rfl,
      Finset.card_image_of_injOn hinj]
    simp [choices, Finset.card_product, Finset.card_powersetCard,
      hc00, hc11, hc01, hc10]
  · intro S hS
    rw [show halves = choices.image join by rfl] at hS
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hS
    rcases Finset.mem_product.mp hq with ⟨hqL, hqR⟩
    rcases Finset.mem_product.mp hqL with ⟨hq00m, hq11m⟩
    rcases Finset.mem_product.mp hqR with ⟨hq01m, hq10m⟩
    exact mme_CW_q6_exact_address_central_cell_union_balanced
      hLG address q.1.1 q.1.2 q.2.1 q.2.2
      (Finset.mem_powersetCard.mp hq00m).1
      (Finset.mem_powersetCard.mp hq11m).1
      (Finset.mem_powersetCard.mp hq01m).1
      (Finset.mem_powersetCard.mp hq10m).1
      (Finset.mem_powersetCard.mp hq00m).2
      (Finset.mem_powersetCard.mp hq11m).2
      (Finset.mem_powersetCard.mp hq01m).2
      (Finset.mem_powersetCard.mp hq10m).2
