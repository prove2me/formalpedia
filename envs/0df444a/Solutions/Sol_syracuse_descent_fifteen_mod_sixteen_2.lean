-- Prove2me | solution 2 for syracuse_descent_fifteen_mod_sixteen
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T11:40:33.419104+00:00
-- url     : https://prove2.me/submissions/ce045b40-cb50-4401-8fd2-0f7a1cf0617f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_syracuse_initial_run_endpoint_and_growth
import Theorems.Thm_syracuse_fifteen_descent_after_initial_run

open Nat

theorem solution (n : ℕ) (h : n % 16 = 15) :
    ∃ t : ℕ, syracuseStep^[t] n < n := by
  let k := (n+1).factorization 2
  let q := ordCompl[2] (n+1)
  have h16 : (2:ℕ)^4 ∣ n+1 := by change 16 ∣ n+1; omega
  have hk : 4 ≤ k := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mp h16
  have hq : 0 < q := Nat.ordCompl_pos 2 (by omega)
  have hodd : ¬2 ∣ q := Nat.not_dvd_ordCompl Nat.prime_two (by omega)
  have e : 2^k*q = n+1 := Nat.ordProj_mul_ordCompl_eq_self (n+1) 2
  have en : 2^k*q-1 = n := by omega
  have ht := (syracuse_initial_run_endpoint_and_growth k q (by omega) hq).1
  rw [en] at ht
  by_cases low : ordCompl[2] (3^k*q-1) < n
  · exact ⟨k, ht.trans_lt low⟩
  · obtain ⟨t, hdrop⟩ := syracuse_fifteen_descent_after_initial_run k q hk hq hodd (by omega)
    exact ⟨t+k, by rwa [Function.iterate_add_apply, ht, ← en]⟩
