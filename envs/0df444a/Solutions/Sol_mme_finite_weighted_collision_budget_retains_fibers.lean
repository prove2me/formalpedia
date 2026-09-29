-- Prove2me | solution 1 for mme_finite_weighted_collision_budget_retains_fibers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T01:04:25.69186+00:00
-- url     : https://prove2.me/submissions/8a800a22-4fcd-4ff3-9729-95b34801fa2e

import Mathlib
import Theorems.Thm_mme_finset_prune_two_mode_collisions_keeps_many_fibers

open BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- A global weighted good-fiber versus collision budget yields one parameter
whose two-mode-isolated remainder retains the requested number of fibers. -/
theorem solution
    {Ω α β γ ζ : Type}
    [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq ζ]
    (E : Ω → Finset α) (x : α → β) (y : α → γ) (z : α → ζ)
    (Good : Ω → Finset ζ) (K H Q R : ℕ)
    (hHK : H ≤ K) (hR : 0 < R)
    (hdegree : ∀ ω, ∀ c ∈ Good ω,
      K ≤ ((E ω).filter (fun e => z e = c)).card)
    (hbudget :
      Fintype.card Ω * ((K - H + 1) * R * Q) +
          R * ∑ ω, (((E ω).product (E ω)).filter (fun p =>
            p.1 ≠ p.2 ∧
              (x p.1 = x p.2 ∨ y p.1 = y p.2))).card ≤
        (K - H + 1) * R * ∑ ω, (Good ω).card) :
    ∃ ω : Ω, ∃ I : Finset α,
      I ⊆ E ω ∧
      (∀ e ∈ I, ∀ e' ∈ E ω,
        x e = x e' ∨ y e = y e' → e = e') ∧
      Q ≤ ((Good ω).filter (fun c =>
        H ≤ (I.filter (fun e => z e = c)).card)).card := by
  classical
  let D : ℕ := K - H + 1
  let collision : Ω → ℕ := fun ω =>
    (((E ω).product (E ω)).filter (fun p =>
      p.1 ≠ p.2 ∧ (x p.1 = x p.2 ∨ y p.1 = y p.2))).card
  let score : Ω → ℕ := fun ω => D * R * (Good ω).card
  have hbudget' :
      ∑ ω, (R * collision ω + D * R * Q) ≤ ∑ ω, score ω := by
    simpa only [D, collision, score, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id,
      Finset.mul_sum, add_comm] using hbudget
  obtain ⟨ω, hωmem, hω⟩ :=
    Finset.exists_le_of_sum_le (s := (Finset.univ : Finset Ω))
      (by simp) hbudget'
  obtain ⟨I, hIE, hisolated, hbad⟩ :=
    mme_finset_prune_two_mode_collisions_keeps_many_fibers
      (E ω) x y z (Good ω) K H hHK (hdegree ω)
  let Ret : Finset ζ := (Good ω).filter (fun c =>
    H ≤ (I.filter (fun e => z e = c)).card)
  let Bad : Finset ζ := (Good ω).filter (fun c =>
    ¬ H ≤ (I.filter (fun e => z e = c)).card)
  have hpart : Ret.card + Bad.card = (Good ω).card := by
    simpa only [Ret, Bad] using
      (Finset.card_filter_add_card_filter_not
        (s := Good ω) (p := fun c =>
          H ≤ (I.filter (fun e => z e = c)).card))
  have hbad' : D * Bad.card ≤ collision ω := by
    simpa only [D, Bad, collision] using hbad
  have hbadScaled : R * (D * Bad.card) ≤ R * collision ω :=
    Nat.mul_le_mul_left R hbad'
  have hpoint : D * R * Q + R * collision ω ≤
      D * R * (Good ω).card := by
    simpa only [score, add_comm] using hω
  have hcancel : D * R * Q + R * collision ω ≤
      D * R * Ret.card + R * collision ω := by
    calc
      D * R * Q + R * collision ω ≤ D * R * (Good ω).card := hpoint
      _ = D * R * Ret.card + R * (D * Bad.card) := by
        rw [← hpart]
        ring
      _ ≤ D * R * Ret.card + R * collision ω := by
        exact Nat.add_le_add_left hbadScaled _
  have hscaled : D * R * Q ≤ D * R * Ret.card :=
    Nat.le_of_add_le_add_right hcancel
  have hDR : 0 < D * R := by
    have hD : 0 < D := by
      dsimp [D]
      omega
    positivity
  have hQR : Q ≤ Ret.card := by
    exact Nat.le_of_mul_le_mul_left hscaled hDR
  exact ⟨ω, I, hIE, hisolated, by simpa only [Ret] using hQR⟩
