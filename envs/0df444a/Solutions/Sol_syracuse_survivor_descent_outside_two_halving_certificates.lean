-- Prove2me | solution 1 for syracuse_survivor_descent_outside_two_halving_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T17:39:07.041647+00:00
-- url     : https://prove2.me/submissions/2dbc6e86-aa9e-49da-9cee-cbb8793eb6b3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_syracuse_mixed_valuation_prefix_descent_certificate
import Theorems.Thm_syracuse_survivor_descent_outside_mixed_prefix_certificates

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
      (3^k*q) % p = (1+2^s) % p ∧ 2+2*(3^d*u) < 2^k*q)) :
    ∃ t : ℕ, syracuseStep^[t] (ordCompl[2] (3^k*q-1)) < 2^k*q-1 := by
  by_cases h : ∃ w : List ℕ, w.head? = some 1 ∧ (∃ a ∈ w, 3 ≤ a) ∧
      (∀ a : ℕ, a ∈ w → 0 < a) ∧
      let y := ordCompl[2] (3^k*q-1)
      let B := 3^w.length*y+syracuseAffineConstant w
      B % 2^(w.sum+1) = 2^w.sum ∧ B < 2^w.sum*(2^k*q-1)
  · obtain ⟨w, _, _, hpos, hmod, hbelow⟩ := h
    exact ⟨w.length, (syracuse_mixed_valuation_prefix_descent_certificate w (ordCompl[2] (3^k*q-1)) (2^k*q-1)
      hpos hmod hbelow).1⟩
  · exact syracuse_survivor_descent_outside_mixed_prefix_certificates k q hk hq hodd hsurvives hmiss houtside hnocert h
