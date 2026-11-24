-- Prove2me | solution 1 for syracuse_fifteen_descent_after_initial_run
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T12:10:23.795134+00:00
-- url     : https://prove2.me/submissions/d9c233f9-73bb-4003-b6cd-d288adf545ef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_syracuse_next_step_descent_single_residue_after_initial_run
import Theorems.Thm_syracuse_survivor_descent_outside_next_step_residues

open Nat

theorem solution (k q : ℕ)
    (hk : 4 ≤ k) (hq : 0 < q) (hodd : ¬2 ∣ q)
    (hsurvives : 2^k*q-1 ≤ ordCompl[2] (3^k*q-1)) :
    ∃ t : ℕ, syracuseStep^[t] (ordCompl[2] (3^k*q-1)) < 2^k*q-1 := by
  by_cases hit : ∃ s b : ℕ, 0 < s ∧ 2^(k+s) < (3:ℕ)^k ∧
      2^(k+s+b) ≤ (3:ℕ)^(k+1) ∧ (3:ℕ)^(k+1) < 2^(k+s+b+1) ∧
      2^(s+b+1)+2^s+3 ≤ q ∧
      (3^(k+1)*q+2^s) % 2^(s+b+1) = 3 % 2^(s+b+1) 
  · obtain ⟨s, b, hs, hu, hl, hh, hsize, he⟩ := hit
    obtain ⟨r, _, code, desc⟩ := syracuse_next_step_descent_single_residue_after_initial_run k s b hs hu hl hh
    have hfall := ((desc q hsize).mpr ((code q).mp he)).2.2
    exact ⟨1, by simpa using hfall⟩
  · exact syracuse_survivor_descent_outside_next_step_residues k q hk hq hodd hsurvives hit
