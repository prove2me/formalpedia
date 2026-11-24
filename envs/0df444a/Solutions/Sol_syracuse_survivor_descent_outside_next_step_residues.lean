-- Prove2me | solution 1 for syracuse_survivor_descent_outside_next_step_residues
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T12:36:54.728725+00:00
-- url     : https://prove2.me/submissions/c56eb86b-b406-439d-b34e-41450293f61e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_syracuse_arbitrarily_delayed_crossing_after_initial_run
import Theorems.Thm_syracuse_survivor_descent_outside_long_contraction_classes

open Nat

theorem solution (k q : ℕ)
    (hk : 4 ≤ k) (hq : 0 < q) (hodd : ¬2 ∣ q)
    (hsurvives : 2^k*q-1 ≤ ordCompl[2] (3^k*q-1))
    (hmiss : ¬∃ s b : ℕ, 0 < s ∧ 2^(k+s) < (3:ℕ)^k ∧
      2^(k+s+b) ≤ (3:ℕ)^(k+1) ∧ (3:ℕ)^(k+1) < 2^(k+s+b+1) ∧
      2^(s+b+1)+2^s+3 ≤ q ∧
      (3^(k+1)*q+2^s) % 2^(s+b+1) = 3 % 2^(s+b+1)) :
    ∃ t : ℕ, syracuseStep^[t] (ordCompl[2] (3^k*q-1)) < 2^k*q-1 := by
  by_cases hit : 6 ≤ k ∧ (3^(k-1)*q) % 4^(2*k+1) = 1
  · obtain ⟨r, _, rule, family⟩ := syracuse_arbitrarily_delayed_crossing_after_initial_run k hit.1
    exact ⟨2*k, (family q hq ((rule q).mp hit.2)).2.1⟩
  · exact syracuse_survivor_descent_outside_long_contraction_classes k q hk hq hodd hsurvives hmiss hit
