-- Prove2me | solution 1 for syracuse_survivor_descent_outside_mixed_prefix_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-25T00:37:34.583694+00:00
-- url     : https://prove2.me/submissions/28029b79-9bbd-44ef-b760-345a2d668ba3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_syracuse_valuation_word_unique_residue_and_affine_progression
import Theorems.Thm_syracuse_survivor_descent_outside_two_step_word_progressions

open Nat

theorem solution (k q : ℕ)
    (hk : 4 ≤ k) (hq : 0 < q) (hodd : ¬2 ∣ q)
    (hsurvives : 2^k*q-1 ≤ ordCompl[2] (3^k*q-1))
    (hmiss : ¬∃ s b : ℕ, 0 < s ∧ 2^(k+s) < (3:ℕ)^k ∧
      2^(k+s+b) ≤ (3:ℕ)^(k+1) ∧ (3:ℕ)^(k+1) < 2^(k+s+b+1) ∧
      2^(s+b+1)+2^s+3 ≤ q ∧
      (3^(k+1)*q+2^s) % 2^(s+b+1) = 3 % 2^(s+b+1))
    (houtside : ¬(6 ≤ k ∧ (3^(k-1)*q) % 4^(2*k+1) = 1))
    (hnocert : ¬(∃ s d : ℕ, 0 < s ∧ 1+2^s < 3^k*q ∧
      let p := 2^(s+1)*4^d
      let u := (3^k*q-(1+2^s))/p
      (3^k*q) % p = (1+2^s) % p ∧ 2+2*(3^d*u) < 2^k*q))
    (hnomixed : ¬(∃ w : List ℕ, w.head? = some 1 ∧ (∃ a ∈ w, 3 ≤ a) ∧
      (∀ a : ℕ, a ∈ w → 0 < a) ∧
      let y := ordCompl[2] (3^k*q-1)
      let B := 3^w.length*y+syracuseAffineConstant w
      B % 2^(w.sum+1) = 2^w.sum ∧ B < 2^w.sum*(2^k*q-1))) :
    ∃ t : ℕ, syracuseStep^[t] (ordCompl[2] (3^k*q-1)) < 2^k*q-1 := by
  by_cases h : ∃ a b : ℕ, 2 ≤ a ∧ 0 < b ∧ a ≠ b ∧
      let y := ordCompl[2] (3^k*q-1)
      let P := 2^(a+b+1)
      let r := y%P
      List.ofFn (fun i : Fin 2 => (3*syracuseStep^[i.val] r+1).factorization 2) = [a,b] ∧
      syracuseStep^[2] r + 18*(y/P) < 2^k*q-1
  · obtain ⟨a,b,ha,hb,_,hw,fall⟩ := h
    let y := ordCompl[2] (3^k*q-1)
    let P := 2^(a+b+1)
    let r := y%P
    have hp : 0 < P := Nat.two_pow_pos _
    have hr : r < P := Nat.mod_lt _ hp
    have hw' : List.ofFn (fun i : Fin 2 =>
        (3*syracuseStep^[i.val] r+1).factorization 2) = [a,b] := hw
    have rule := syracuse_valuation_word_unique_residue_and_affine_progression
      [a,b] (by simp) (by simp; omega)
    change ∃ u < P,
      (∀ x : ℕ, x%P=u ↔ List.ofFn (fun i : Fin 2 =>
        (3*syracuseStep^[i.val] x+1).factorization 2) = [a,b]) ∧
      (∀ m : ℕ, syracuseStep^[2] (u+P*m) = syracuseStep^[2] u+18*m) at rule
    obtain ⟨u,_,spec,lift⟩ := rule
    have eqn : r=u := (Nat.mod_eq_of_lt hr).symm.trans ((spec r).mpr hw')
    have ev := lift (y/P)
    rw [← eqn, show r+P*(y/P)=y from Nat.mod_add_div _ _] at ev
    exact ⟨2, ev.trans_lt fall⟩
  · exact syracuse_survivor_descent_outside_two_step_word_progressions k q hk hq hodd hsurvives hmiss houtside hnocert hnomixed h
