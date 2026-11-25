-- Prove2me | solution 1 for ppp_factors_through_commuting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:01:23.117799+00:00
-- url     : https://prove2.me/submissions/2e8cbdea-b3dd-4dbe-b98b-2bdb27b53516

module
public import Mathlib
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_Counting
public import Definitions.Def_SCCThm8_Numeric
public import Definitions.Def_SCCThm8_Degeneration
public import Definitions.Def_SCCThm8_PowerDegeneration
public import Definitions.Def_SCCGroupBarrier_Solution
public import Theorems.Thm_SCCThm8_rigidity


set_option autoImplicit true
@[expose] public section
public section
open Finset
theorem _root_.solution {G : Type*} [Group G] (k : ℕ) (hk : 2 ≤ k)
    (f₁ f₂ f₃ : Finset (Fin (3 * k)) → G)
    (hP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C → f₁ A * f₂ B * f₃ C = 1) :
    ∃ g : Fin (3 * k) → G, (∀ i j, Commute (g i) (g j)) ∧
      ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
        f₁ A * f₂ B * f₃ C =
          ((List.finRange (3 * k)).map fun i =>
            g i ^ ((if i ∈ A then 1 else 0) + (if i ∈ B then 1 else 0) +
              (if i ∈ C then 1 else 0) - 1 : ℤ)).prod :=
  SCCThm8.rigidity k hk f₁ f₂ f₃ hP
