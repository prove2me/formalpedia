-- Prove2me | solution 1 for ppp_card_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:01:20.554453+00:00
-- url     : https://prove2.me/submissions/0a341cfc-885e-48ad-b6e9-3460788bdc4a

module
public import Mathlib
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_Counting
public import Definitions.Def_SCCThm8_Numeric
public import Definitions.Def_SCCThm8_Degeneration
public import Definitions.Def_SCCThm8_PowerDegeneration
public import Definitions.Def_SCCGroupBarrier_Solution
public import Theorems.Thm_mult_eq_one_of_disjoint
public import Theorems.Thm_SCCThm8_card_bound
public import Theorems.Thm_SCCThm8_realizable
public import Theorems.Thm_SCCThm8_rigidity


set_option autoImplicit true
@[expose] public section
public section
open Finset
theorem _root_.solution {G : Type*} [Group G] [Fintype G] (k : ℕ) (hk : 2 ≤ k)
    (f₁ f₂ f₃ : Finset (Fin (3 * k)) → G)
    (hPPP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      (f₁ A * f₂ B * f₃ C = 1 ↔ Disjoint A B ∧ Disjoint A C ∧ Disjoint B C)) :
    2 ^ (3 * k - 1) ≤ Fintype.card G := by
  obtain ⟨g, hc, hprod⟩ := SCCThm8.rigidity k hk f₁ f₂ f₃
    (fun A B C hA hB hC h1 h2 h3 => (hPPP A B C hA hB hC).mpr ⟨h1, h2, h3⟩)
  refine SCCThm8.card_bound (by omega) g hc ?_
  intro e hr hs hne h1
  obtain ⟨A, B, C, hA, hB, hC, hm⟩ := SCCThm8.realizable k (fun i => e i + 1)
    (fun i => by have := hr i; constructor <;> omega)
    (by rw [Finset.sum_add_distrib, hs]; simp)
  have hone : f₁ A * f₂ B * f₃ C = 1 := by
    rw [hprod A B C hA hB hC]
    have : (fun i => SCCThm8.mult A B C i - 1) = e := by
      funext i; rw [hm i]; ring
    rw [this]; exact h1
  obtain ⟨h1', h2', h3'⟩ := (hPPP A B C hA hB hC).mp hone
  apply hne
  funext i
  have := mult_eq_one_of_disjoint k A B C hA hB hC h1' h2' h3' i
  rw [hm i] at this
  simp only [Pi.zero_apply]
  omega
