-- Prove2me | solution 1 for sumfree_set_density
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T00:41:04.312571+00:00
-- url     : https://prove2.me/submissions/a8c71d24-f53d-48f8-9782-0868c7dc0407

import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solution :
    ∀ eps : ℝ, 0 < eps →
    ∀ (n : ℕ) (A : Finset (Fin n)),
      (∀ a b c : Fin n, a ∈ A → b ∈ A → c ∈ A → a.val + b.val ≠ c.val) →
      (A.card : ℝ) ≤ (n : ℝ) / 2 + eps := by
  intro eps heps n A hsum
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  let c := A.max' hA
  have hc : c ∈ A := A.max'_mem hA
  have hle {a : Fin n} (ha : a ∈ A) : a.val ≤ c.val := Finset.le_max' A a ha
  let f : Fin n → Fin n := fun a => ⟨c.val - a.val, (Nat.sub_le _ _).trans_lt c.isLt⟩
  have hinj : Set.InjOn f A := by
    intro a ha b hb hab
    have hvals := congrArg Fin.val hab
    have ha' := hle ha
    have hb' := hle hb
    apply Fin.ext
    dsimp [f] at hvals
    omega
  have hdis : Disjoint A (A.image f) := by
    apply Finset.disjoint_left.mpr
    intro a ha hfa
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hfa
    have hvals := congrArg Fin.val hba
    have hb' := hle hb
    apply hsum b a c hb ha hc
    dsimp [f] at hvals
    omega
  have hcard : 2 * A.card ≤ n := by
    have hbound := Finset.card_le_card (Finset.subset_univ (A ∪ A.image f))
    rw [Finset.card_union_of_disjoint hdis, Finset.card_image_of_injOn hinj,
      Finset.card_univ, Fintype.card_fin] at hbound
    omega
  have hcardReal : (2 : ℝ) * A.card ≤ n := by exact_mod_cast hcard
  linarith

#print axioms solution
