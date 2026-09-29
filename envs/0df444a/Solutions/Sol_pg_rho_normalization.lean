-- Prove2me | solution 1 for pg_rho_normalization
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-10T04:29:11.629457+00:00
-- url     : https://prove2.me/submissions/b8fb7f4a-0df8-483d-b193-0801f1ca6e72

import Definitions.Def_pg_mdp_core
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open Finset

theorem solution : ∀ {S A : Type} [Fintype S] [Fintype A] [DecidableEq S] (P : S → A → S → ℝ) (π : ℝ → S → A → ℝ) (θ : ℝ) (hP : ∀ s a, ∑ s' : S, P s a s' = 1) (hπ : ∀ s, ∑ a : A, π θ s a = 1), ∀ (t : ℕ) (s₀ : S), ∑ s : S, pgRho P π t s₀ θ s = 1 := by
  intro S A _ _ _ P π θ hP hπ t
  induction t with
  | zero =>
    intro s₀
    calc (∑ s : S, pgRho P π 0 s₀ θ s)
        = ∑ s : S, (if s = s₀ then (1:ℝ) else 0) := by
          apply Finset.sum_congr rfl; intro s _; rfl
      _ = 1 := by rw [Finset.sum_ite_eq' Finset.univ s₀]; simp
  | succ m ih =>
    intro s₀
    calc (∑ s : S, pgRho P π (m + 1) s₀ θ s)
        = ∑ s : S, ∑ s' : S, (∑ a : A, π θ s₀ a * P s₀ a s') * pgRho P π m s' θ s := by
          apply Finset.sum_congr rfl; intro s _; rfl
      _ = ∑ s' : S, ∑ s : S, (∑ a : A, π θ s₀ a * P s₀ a s') * pgRho P π m s' θ s := Finset.sum_comm
      _ = ∑ s' : S, (∑ a : A, π θ s₀ a * P s₀ a s') * ∑ s : S, pgRho P π m s' θ s := by
          apply Finset.sum_congr rfl; intro s' _; rw [Finset.mul_sum]
      _ = ∑ s' : S, (∑ a : A, π θ s₀ a * P s₀ a s') * 1 := by
          apply Finset.sum_congr rfl; intro s' _; rw [ih s']
      _ = ∑ s' : S, ∑ a : A, π θ s₀ a * P s₀ a s' := by
          apply Finset.sum_congr rfl; intro s' _; ring
      _ = ∑ a : A, ∑ s' : S, π θ s₀ a * P s₀ a s' := Finset.sum_comm
      _ = ∑ a : A, π θ s₀ a * ∑ s' : S, P s₀ a s' := by
          apply Finset.sum_congr rfl; intro a _; rw [Finset.mul_sum]
      _ = ∑ a : A, π θ s₀ a * 1 := by
          apply Finset.sum_congr rfl; intro a _; rw [hP s₀ a]
      _ = ∑ a : A, π θ s₀ a := by apply Finset.sum_congr rfl; intro a _; ring
      _ = 1 := hπ s₀
