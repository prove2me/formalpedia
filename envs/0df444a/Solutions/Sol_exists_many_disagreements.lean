-- Prove2me | solution 1 for exists_many_disagreements
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:37:35.106949+00:00
-- url     : https://prove2.me/submissions/3569b352-338a-47d6-b6c1-60e32b0fc1d5

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Theorems.Thm_disagreement_sum_eq

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution {α : Type*} [Fintype α]
    (h : α → Bool) (hcard : 2 ≤ Fintype.card α) :
    ∃ f : α → Bool,
      Fintype.card α < 4 * (Finset.univ.filter fun x => f x ≠ h x).card := by
  classical
  -- Average disagreement count = |α|/2.
  -- We show: |α|/2 > |α|/4 (since |α| ≥ 2), so some f has > |α|/4.
  -- More precisely: ∑_f count(f) = |α| * 2^(|α|-1).
  -- If all counts ≤ |α|/4, i.e., 4*count ≤ |α|:
  -- ∑_f count ≤ Fintype.card (α → Bool) * |α|/4 = 2^|α| * |α| / 4 = |α| * 2^(|α|-2).
  -- But ∑_f count = |α| * 2^(|α|-1) = |α| * 2^(|α|-2) * 2. Contradiction when |α| ≥ 2.
  by_contra H
  push Not at H
  -- H : ∀ f, 4 * count(f) ≤ |α| , i.e., |α| is NOT < 4 * count(f)
  -- Actually H : ∀ f, ¬ (|α| < 4 * count(f)), i.e., 4 * count(f) ≤ |α|
  have H' : ∀ f : α → Bool,
      (Finset.univ.filter fun x => f x ≠ h x).card ≤ Fintype.card α / 4 := by
    intro f
    have := H f
    omega
  -- Sum bound: ∑_f count(f) ≤ 2^|α| * (|α|/4)
  have hsum_le : ∑ f : α → Bool,
      (Finset.univ.filter fun x => f x ≠ h x).card ≤
      Fintype.card (α → Bool) * (Fintype.card α / 4) := by
    calc ∑ f : α → Bool, (Finset.univ.filter fun x => f x ≠ h x).card
        ≤ ∑ _f : α → Bool, Fintype.card α / 4 :=
          Finset.sum_le_sum fun f _ => H' f
      _ = Fintype.card (α → Bool) * (Fintype.card α / 4) := by
          simp [Finset.sum_const, Finset.card_univ]
  -- But the true sum = |α| * 2^(|α|-1)
  have hsum_eq := disagreement_sum_eq h
  -- Need: |α| * 2^(|α|-1) ≤ 2^|α| * (|α|/4) leads to contradiction
  -- 2^|α| = 2 * 2^(|α|-1), so RHS = 2 * 2^(|α|-1) * (|α|/4)
  -- LHS = |α| * 2^(|α|-1)
  -- So need |α| ≤ 2 * (|α|/4) = |α|/2, i.e., |α|/2 ≤ 0. False for |α| ≥ 2.
  rw [hsum_eq] at hsum_le
  have hcard_fun : Fintype.card (α → Bool) = 2 ^ Fintype.card α := by
    rw [Fintype.card_fun, Fintype.card_bool]
  rw [hcard_fun] at hsum_le
  -- hsum_le: n * 2^(n-1) ≤ 2^n * (n/4) where n = Fintype.card α ≥ 2
  set n := Fintype.card α with hn
  -- 2^n = 2 * 2^(n-1) for n ≥ 1
  have hn_pos : 1 ≤ n := by omega
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    have : n = n - 1 + 1 := by omega
    conv_lhs => rw [this]
    ring
  rw [hpow] at hsum_le
  -- hsum_le: n * 2^(n-1) ≤ 2 * 2^(n-1) * (n/4)
  have hpow_pos : 0 < 2 ^ (n - 1) := Nat.pos_of_ne_zero (by positivity)
  -- Cancel 2^(n-1) from both sides
  have key : n ≤ 2 * (n / 4) := Nat.le_of_mul_le_mul_right
    (by linarith [hsum_le] : n * 2 ^ (n - 1) ≤ (2 * (n / 4)) * 2 ^ (n - 1))
    hpow_pos
  -- But n ≥ 2 and 2*(n/4) ≤ n/2 < n for n ≥ 2.
  omega
