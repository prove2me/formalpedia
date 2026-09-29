-- Prove2me | solution 1 for crossing_residue_cardinality
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-09T04:42:29.664091+00:00
-- url     : https://prove2.me/submissions/e2183c4c-60d6-45c9-8610-72bae9862813

/-
  Standalone producer for the finite crossing-residue cardinality bound.
  The prefix cardinality is imported through its accepted platform mirror;
  no project-local prefix-count implementation is imported here.
-/

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.Card
import Theorems.Thm_positive_exponent_prefix_cardinality

set_option autoImplicit false

open scoped BigOperators
open Classical

private theorem card_le_pow_mul_of_label_modEq
    (b n' : ℕ) (hn'b : n' ≤ b)
    (A : Type*) [Fintype A]
    (S : Finset (Fin (2 ^ b)))
    (label : {x // x ∈ S} → A)
    (hlabel : ∀ x y, label x = label y → Nat.ModEq (2 ^ n') x.1.1 y.1.1) :
    S.card ≤ 2 ^ (b - n') * Fintype.card A := by
  let q : ℕ := 2 ^ n'
  let r : ℕ := 2 ^ (b - n')
  have hqpos : 0 < q := by
    dsimp [q]
    have hpowpos : ∀ t : ℕ, 0 < 2 ^ t := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
          simpa [Nat.pow_succ] using Nat.mul_pos ih (by decide : 0 < 2)
    exact hpowpos n'
  have hpow : q * r = 2 ^ b := by
    dsimp [q, r]
    rw [← pow_add]
    congr 1
    omega
  let encode : {x // x ∈ S} → A × Fin r := fun x =>
    (label x, ⟨x.1.1 / q, by
      apply (Nat.div_lt_iff_lt_mul hqpos).2
      calc
        x.1.1 < 2 ^ b := x.1.isLt
        _ = q * r := hpow.symm
        _ = r * q := Nat.mul_comm _ _⟩)
  have hinj : Function.Injective encode := by
    intro x y hxy
    have hlabels : label x = label y := by
      simpa [encode] using congrArg Prod.fst hxy
    have hquot : x.1.1 / q = y.1.1 / q := by
      simpa [encode] using congrArg (fun p : A × Fin r => p.2.val) hxy
    have hrem : x.1.1 % q = y.1.1 % q := by
      simpa [Nat.ModEq] using hlabel x y hlabels
    apply Subtype.ext
    apply Fin.ext
    calc
      x.1.1 = x.1.1 % q + q * (x.1.1 / q) := (Nat.mod_add_div _ _).symm
      _ = y.1.1 % q + q * (y.1.1 / q) := by rw [hrem, hquot]
      _ = y.1.1 := Nat.mod_add_div _ _
  calc
    S.card = Fintype.card {x // x ∈ S} := by simp
    _ ≤ Fintype.card (A × Fin r) := Fintype.card_le_of_injective encode hinj
    _ = r * Fintype.card A := by simp [Nat.mul_comm]
    _ = 2 ^ (b - n') * Fintype.card A := by rfl

theorem solution
    (b n' t : ℕ) (hn' : 0 < n') (hn'b : n' ≤ b)
    (S : Finset (Fin (2 ^ b)))
    (label : {x // x ∈ S} →
      Σ k : Fin t, {a : Fin k → Fin n' //
        (∀ i, 0 < (a i).val) ∧ (∑ i, (a i).val) < n'})
    (hlabel : ∀ x y, label x = label y → Nat.ModEq (2 ^ n') x.1.1 y.1.1) :
    S.card ≤ 2 ^ (b - n') *
      (∑ k : Fin t, Nat.choose (n' - 1) k) := by
  have h := card_le_pow_mul_of_label_modEq b n' hn'b
    (Σ k : Fin t, {a : Fin k → Fin n' //
      (∀ i, 0 < (a i).val) ∧ (∑ i, (a i).val) < n'}) S label hlabel
  have hcard : Fintype.card
      (Σ k : Fin t, {a : Fin k → Fin n' //
        (∀ i, 0 < (a i).val) ∧ (∑ i, (a i).val) < n'}) =
      ∑ k : Fin t, Nat.choose (n' - 1) k := by
    rw [Fintype.card_sigma]
    apply Finset.sum_congr rfl
    intro k hk
    exact positive_exponent_prefix_cardinality k n' hn'
  rw [hcard] at h
  exact h

#print axioms solution
