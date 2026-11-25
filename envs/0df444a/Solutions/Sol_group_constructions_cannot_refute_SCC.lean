-- Prove2me | solution 1 for group_constructions_cannot_refute_SCC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:10:25.10459+00:00
-- url     : https://prove2.me/submissions/21f8cc64-ac1f-44ce-b757-e717700313ab

module
public import Mathlib
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_Counting
public import Definitions.Def_SCCThm8_Numeric
public import Definitions.Def_SCCThm8_Degeneration
public import Definitions.Def_SCCThm8_PowerDegeneration
public import Definitions.Def_SCCGroupBarrier_Solution
public import Theorems.Thm_SCCThm8_power_deg_card_ge
public import Theorems.Thm_SCCThm8_tau_lt_central


set_option autoImplicit true
@[expose] public section
public section
open Finset
theorem _root_.solution {G : Type*} [Group G] [Fintype G]
    (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m)
    (f₁ f₂ f₃ : (Fin m → Finset (Fin (3 * k))) → G) (a b c : (Fin m → Finset (Fin (3 * k))) → ℤ)
    (hpart : ∀ A B C : Fin m → Finset (Fin (3 * k)),
      (∀ j, (A j).card = k) → (∀ j, (B j).card = k) → (∀ j, (C j).card = k) →
      (∀ j, Disjoint (A j) (B j) ∧ Disjoint (A j) (C j) ∧ Disjoint (B j) (C j)) →
        f₁ A * f₂ B * f₃ C = 1 ∧ a A + b B + c C = 0)
    (hnon : ∀ A B C : Fin m → Finset (Fin (3 * k)),
      (∀ j, (A j).card = k) → (∀ j, (B j).card = k) → (∀ j, (C j).card = k) →
      ¬ (∀ j, Disjoint (A j) (B j) ∧ Disjoint (A j) (C j) ∧ Disjoint (B j) (C j)) →
        f₁ A * f₂ B * f₃ C = 1 → 0 < a A + b B + c C) :
    ((8 ^ k * (Nat.choose (3 * k) k) * (Nat.choose (2 * k) k) : ℚ) / 27 ^ k) ^ m <
      Fintype.card G := by
  have h1 := SCCThm8.tau_lt_central k (by omega)
  have h2 := SCCThm8.power_deg_card_ge k m hk f₁ f₂ f₃ a b c hpart hnon
  have h0 : (0 : ℚ) ≤ SCCThm8.tau k := by unfold SCCThm8.tau; positivity
  have h3 : SCCThm8.tau k ^ m < ((Nat.choose (3 * k) (3 * k / 2) : ℕ) : ℚ) ^ m :=
    pow_lt_pow_left₀ h1 h0 (by omega)
  have h2' : ((Nat.choose (3 * k) (3 * k / 2) ^ m : ℕ) : ℚ) ≤ (Fintype.card G : ℚ) := by
    exact_mod_cast h2
  push_cast at h2'
  unfold SCCThm8.tau at h3
  linarith
