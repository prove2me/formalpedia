-- Prove2me | solution 1 for group_construction_exceeds_SCC_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:02:35.162914+00:00
-- url     : https://prove2.me/submissions/555cd5ef-0ec2-4d4e-a8f3-bd381f1e55c8

module
public import Mathlib
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_Counting
public import Definitions.Def_SCCThm8_Numeric
public import Definitions.Def_SCCThm8_Degeneration
public import Definitions.Def_SCCThm8_PowerDegeneration
public import Definitions.Def_SCCGroupBarrier_Solution
public import Theorems.Thm_ppp_card_ge
public import Theorems.Thm_SCCThm8_tau_lt_two_pow


set_option autoImplicit true
@[expose] public section
public section
open Finset
theorem _root_.solution {G : Type*} [Group G] [Fintype G]
    (k : ℕ) (hk : 2 ≤ k) (f₁ f₂ f₃ : Finset (Fin (3 * k)) → G)
    (hPPP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      (f₁ A * f₂ B * f₃ C = 1 ↔ Disjoint A B ∧ Disjoint A C ∧ Disjoint B C)) :
    (8 ^ k * (Nat.choose (3 * k) k) * (Nat.choose (2 * k) k) : ℚ) / 27 ^ k <
      Fintype.card G := by
  have h1 := SCCThm8.tau_lt_two_pow k hk
  have h2 := ppp_card_ge k hk f₁ f₂ f₃ hPPP
  have h2' : ((2 ^ (3 * k - 1) : ℕ) : ℚ) ≤ (Fintype.card G : ℚ) := by exact_mod_cast h2
  unfold SCCThm8.tau at h1
  push_cast at h2'
  linarith
