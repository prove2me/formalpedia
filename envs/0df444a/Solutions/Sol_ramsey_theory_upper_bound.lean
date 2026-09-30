-- Prove2me | solution 1 for ramsey_theory_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:22:12.51195+00:00
-- url     : https://prove2.me/submissions/e63515fe-84ff-4af0-9202-bc099c6c6de7

import Mathlib

private theorem insert_monochromatic {α : Type*} [DecidableEq α]
    (col : α → α → Bool) (hsymm : ∀ a b, col a b = col b a)
    (color : Bool) (x : α) (T : Finset α)
    (hT : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → col a b = color)
    (hx : ∀ a ∈ T, col x a = color) :
    ∀ a ∈ insert x T, ∀ b ∈ insert x T, a ≠ b → col a b = color := by
  intro a ha b hb hab
  rcases Finset.mem_insert.mp ha with hax | haT
  · rcases Finset.mem_insert.mp hb with hbx | hbT
    · exact False.elim (hab (hax.trans hbx.symm))
    · simpa only [hax] using hx b hbT
  · rcases Finset.mem_insert.mp hb with hbx | hbT
    · rw [hbx, hsymm a x]
      exact hx a haT
    · exact hT a haT b hbT hab

-- Off-diagonal recursion keeps both color targets available after deleting a vertex.
private theorem finite_ramsey_bound {α : Type*} [DecidableEq α]
    (col : α → α → Bool) (hsymm : ∀ a b, col a b = col b a) :
    ∀ r s : ℕ, ∀ S : Finset α, 2 ^ (r + s) ≤ S.card →
      (∃ T ⊆ S, T.card = r ∧
        ∀ a ∈ T, ∀ b ∈ T, a ≠ b → col a b = true) ∨
      (∃ T ⊆ S, T.card = s ∧
        ∀ a ∈ T, ∀ b ∈ T, a ≠ b → col a b = false) := by
  intro r
  induction r with
  | zero =>
      intro s S hS
      exact Or.inl ⟨∅, Finset.empty_subset S, rfl, by simp⟩
  | succ r ihr =>
      intro s
      induction s with
      | zero =>
          intro S hS
          exact Or.inr ⟨∅, Finset.empty_subset S, rfl, by simp⟩
      | succ s ihs =>
          intro S hS
          have hpos : 0 < S.card := lt_of_lt_of_le (by positivity) hS
          obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
          let R := (S.erase x).filter (fun y => col x y = true)
          let B := (S.erase x).filter (fun y => col x y ≠ true)
          have hpartition : R.card + B.card = (S.erase x).card := by
            exact Finset.card_filter_add_card_filter_not _
          have herase : (S.erase x).card = S.card - 1 := Finset.card_erase_of_mem hx
          have hpower : 2 ^ (r + 1 + (s + 1)) = 2 * 2 ^ (r + s + 1) := by
            rw [show r + 1 + (s + 1) = (r + s + 1) + 1 by omega, pow_succ]
            omega
          have hlarge : 2 ^ (r + s + 1) ≤ R.card ∨ 2 ^ (r + s + 1) ≤ B.card := by
            rw [hpower] at hS
            omega
          rcases hlarge with hR | hB
          · have hR' : 2 ^ (r + (s + 1)) ≤ R.card := by simpa [Nat.add_assoc] using hR
            rcases ihr (s + 1) R hR' with ⟨T, hTR, hcard, hmono⟩ | ⟨T, hTR, hcard, hmono⟩
            · left
              have hxT : x ∉ T := by
                intro h
                exact (Finset.mem_erase.mp (Finset.mem_filter.mp (hTR h)).1).1 rfl
              refine ⟨insert x T, ?_, ?_, insert_monochromatic col hsymm true x T hmono ?_⟩
              · exact Finset.insert_subset hx (fun y hy =>
                  Finset.mem_of_mem_erase (Finset.mem_filter.mp (hTR hy)).1)
              · simp [Finset.card_insert_of_notMem hxT, hcard]
              · intro y hy
                exact (Finset.mem_filter.mp (hTR hy)).2
            · exact Or.inr ⟨T, (fun y hy =>
                Finset.mem_of_mem_erase (Finset.mem_filter.mp (hTR hy)).1), hcard, hmono⟩
          · have hB' : 2 ^ (r + 1 + s) ≤ B.card := by simpa [Nat.add_right_comm] using hB
            rcases ihs B hB' with ⟨T, hTB, hcard, hmono⟩ | ⟨T, hTB, hcard, hmono⟩
            · exact Or.inl ⟨T, (fun y hy =>
                Finset.mem_of_mem_erase (Finset.mem_filter.mp (hTB hy)).1), hcard, hmono⟩
            · right
              have hxT : x ∉ T := by
                intro h
                exact (Finset.mem_erase.mp (Finset.mem_filter.mp (hTB h)).1).1 rfl
              refine ⟨insert x T, ?_, ?_, insert_monochromatic col hsymm false x T hmono ?_⟩
              · exact Finset.insert_subset hx (fun y hy =>
                  Finset.mem_of_mem_erase (Finset.mem_filter.mp (hTB hy)).1)
              · simp [Finset.card_insert_of_notMem hxT, hcard]
              · intro y hy
                exact Bool.eq_false_iff.mpr (Finset.mem_filter.mp (hTB hy)).2

theorem solution (k : ℕ) (hk : 2 ≤ k) :
    ∃ N : ℕ, N ≤ 4 ^ k ∧
    ∀ (n : ℕ) (_ : N ≤ n) (col : Sym2 (Fin n) → Bool),
      (∃ S : Finset (Fin n), S.card = k ∧
        ∀ a ∈ S, ∀ b ∈ S, a ≠ b → col (Sym2.mk a b) = true) ∨
      (∃ S : Finset (Fin n), S.card = k ∧
        ∀ a ∈ S, ∀ b ∈ S, a ≠ b → col (Sym2.mk a b) = false) := by
  refine ⟨4 ^ k, le_rfl, ?_⟩
  intro n hn col
  have hpow : 2 ^ (k + k) = 4 ^ k := by
    rw [pow_add, ← mul_pow]
    norm_num
  have hcard : 2 ^ (k + k) ≤ (Finset.univ : Finset (Fin n)).card := by
    simpa [hpow] using hn
  have hsymm : ∀ a b : Fin n, col (Sym2.mk a b) = col (Sym2.mk b a) := by
    intro a b
    congr 1
    exact Sym2.eq_swap
  rcases finite_ramsey_bound (fun a b => col (Sym2.mk a b)) hsymm k k Finset.univ hcard with
    ⟨S, _, hsize, hmono⟩ | ⟨S, _, hsize, hmono⟩
  · exact Or.inl ⟨S, hsize, hmono⟩
  · exact Or.inr ⟨S, hsize, hmono⟩

#check @solution
#print axioms solution
