-- Prove2me | solution 1 for disagreement_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:34:27.539647+00:00
-- url     : https://prove2.me/submissions/23c2d311-ddc8-474a-871d-f2dba1ea9d7a

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core

set_option autoImplicit true
@[expose] public section
public section
universe u v
open Finset
theorem _root_.solution {α : Type*} [Fintype α] [DecidableEq α]
    (h : α → Bool) :
    ∑ f : α → Bool,
      (univ.filter fun x => f x ≠ h x).card =
    Fintype.card α * 2 ^ (Fintype.card α - 1) := by
  -- Swap order of summation: ∑_f #{x | f x ≠ h x} = ∑_x #{f | f x ≠ h x}
  conv_lhs =>
    arg 2; ext f
    rw [show (univ.filter fun x => f x ≠ h x).card =
      ∑ x : α, if f x ≠ h x then 1 else 0 from by
        simp [card_filter]]
  rw [sum_comm]
  -- For each x, #{f | f x ≠ h x} = 2^(|α|-1)
  -- because fixing f(x) = !(h x) and varying f on α\{x} gives 2^(|α|-1) functions
  suffices ∀ x : α, ∑ f : α → Bool, (if f x ≠ h x then 1 else 0) =
      2 ^ (Fintype.card α - 1) by
    simp only [this, sum_const, card_univ, smul_eq_mul]
  intro x
  -- Need: #{f : α → Bool | f x ≠ h x} = 2^(|α|-1)
  -- The functions f with f(x) ≠ h(x) are in bijection with (α \ {x}) → Bool
  -- via restriction, since f(x) is forced to be !(h x).
  -- Rewrite the sum as a filter cardinality
  rw [show (∑ f : α → Bool, if f x ≠ h x then (1 : ℕ) else 0) =
      (univ.filter fun f : α → Bool => f x ≠ h x).card from by
        rw [card_filter]]
  -- Now show #{f | f x ≠ h x} = 2^(|α|-1)
  -- Bijection: { f | f x ≠ h x } ≃ ({ y : α // y ≠ x } → Bool)
  -- because f(x) is forced to be !h(x), f on the rest is free.
  rw [show (univ.filter fun f : α → Bool => f x ≠ h x).card =
      Fintype.card ({ y : α // y ≠ x } → Bool) from by
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    calc ↥(univ.filter fun f : α → Bool => f x ≠ h x)
        ≃ { f : α → Bool // f x ≠ h x } := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact (Equiv.subtypeEquivProp (by simp)).symm
      _ ≃ ({ y : α // y ≠ x } → Bool) :=
          { toFun := fun ⟨f, hf⟩ y => f y.val
            invFun := fun g => ⟨fun y => if hyx : y = x then !h x else g ⟨y, hyx⟩,
                                 by simp⟩
            left_inv := by
              intro ⟨f, hf⟩
              simp only [Subtype.mk.injEq]
              funext y
              split_ifs with hyx
              · -- y = x case: need !h y = f y (after subst x = y)
                subst hyx
                -- hf : f y ≠ h y, goal: !h y = f y
                cases hfx : f y <;> cases hhx : h y <;> simp_all
              · -- y ≠ x case: trivial
                rfl
            right_inv := by
              intro g; ext ⟨y, hy⟩; simp [hy] }]
  simp_all
