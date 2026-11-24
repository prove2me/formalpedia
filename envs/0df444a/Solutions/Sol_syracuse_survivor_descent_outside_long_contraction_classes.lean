-- Prove2me | solution 1 for syracuse_survivor_descent_outside_long_contraction_classes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T17:05:33.221376+00:00
-- url     : https://prove2.me/submissions/b5faa80d-c9b3-494e-9d57-e1c0f16acd6f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_syracuse_initial_run_block_crossing_certificate
import Theorems.Thm_syracuse_survivor_descent_outside_two_halving_certificates

open Nat

theorem solution (k q : ℕ)
    (hk : 4 ≤ k) (hq : 0 < q) (hodd : ¬2 ∣ q)
    (hsurvives : 2^k*q-1 ≤ ordCompl[2] (3^k*q-1))
    (hmiss : ¬∃ s b : ℕ, 0 < s ∧ 2^(k+s) < (3:ℕ)^k ∧
      2^(k+s+b) ≤ (3:ℕ)^(k+1) ∧ (3:ℕ)^(k+1) < 2^(k+s+b+1) ∧
      2^(s+b+1)+2^s+3 ≤ q ∧
      (3^(k+1)*q+2^s) % 2^(s+b+1) = 3 % 2^(s+b+1))
    (houtside : ¬(6 ≤ k ∧ (3^(k-1)*q) % 4^(2*k+1) = 1)) :
    ∃ t : ℕ, syracuseStep^[t] (ordCompl[2] (3^k*q-1)) < 2^k*q-1 := by
  by_cases h : ∃ s d : ℕ, 0 < s ∧ 1+2^s < 3^k*q ∧
      let p := 2^(s+1)*4^d
      let u := (3^k*q-(1+2^s))/p
      (3^k*q) % p = (1+2^s) % p ∧ 2+2*(3^d*u) < 2^k*q
  · obtain ⟨s,d,hs,hgt,hmod,hsmall⟩ := h
    have eqv := syracuse_initial_run_block_crossing_certificate k q s d hs hgt
    dsimp only at eqv
    exact ⟨d, (eqv.2 hmod).2.mpr hsmall⟩
  · exact syracuse_survivor_descent_outside_two_halving_certificates k q hk hq hodd hsurvives hmiss houtside h
