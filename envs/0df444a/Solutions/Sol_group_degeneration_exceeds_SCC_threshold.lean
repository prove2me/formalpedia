-- Prove2me | solution 1 for group_degeneration_exceeds_SCC_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:03:06.366315+00:00
-- url     : https://prove2.me/submissions/8e7f16f4-6366-41c5-9354-3c3e93c9400a

module
public import Mathlib
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_Counting
public import Definitions.Def_SCCThm8_Numeric
public import Definitions.Def_SCCThm8_Degeneration
public import Definitions.Def_SCCThm8_PowerDegeneration
public import Definitions.Def_SCCGroupBarrier_Solution
public import Theorems.Thm_SCCThm8_deg_card_ge
public import Theorems.Thm_SCCThm8_tau_lt_central


set_option autoImplicit true
@[expose] public section
public section
open Finset
theorem _root_.solution {G : Type*} [Group G] [Fintype G]
    (k : ℕ) (hk : 2 ≤ k) (f₁ f₂ f₃ : Finset (Fin (3 * k)) → G) (a b c : Finset (Fin (3 * k)) → ℤ)
    (hpart : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C →
        f₁ A * f₂ B * f₃ C = 1 ∧ a A + b B + c C = 0)
    (hnon : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      ¬ (Disjoint A B ∧ Disjoint A C ∧ Disjoint B C) →
        f₁ A * f₂ B * f₃ C = 1 → 0 < a A + b B + c C) :
    (8 ^ k * (Nat.choose (3 * k) k) * (Nat.choose (2 * k) k) : ℚ) / 27 ^ k <
      Fintype.card G := by
  have h1 := SCCThm8.tau_lt_central k (by omega)
  have h2 := SCCThm8.deg_card_ge k hk f₁ f₂ f₃ a b c hpart hnon
  have h2' : ((Nat.choose (3 * k) (3 * k / 2) : ℕ) : ℚ) ≤ (Fintype.card G : ℚ) := by
    exact_mod_cast h2
  unfold SCCThm8.tau at h1
  linarith
