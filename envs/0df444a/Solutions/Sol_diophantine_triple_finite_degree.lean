-- Prove2me | solution 1 for diophantine_triple_finite_degree
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-07T04:06:30.26368+00:00
-- url     : https://prove2.me/submissions/c6323185-506d-4a27-928e-9e6d21e7bfa3

import Theorems.Thm_diophantine_descent_step_exists
import Definitions.Def_diophantine_descent
import Mathlib.Data.Nat.Init
set_option autoImplicit false
open DiophantineDescent

theorem solution (a b c : Nat) (h : Triple a b c) :
    ∃ n : Nat, HasDegree a b c n :=
  @Nat.strong_induction_on (fun c => ∀ a b : Nat, Triple a b c → ∃ n : Nat, HasDegree a b c n) c
    (fun c ih a b h => by
      by_cases hE : Euler a b c
      · exact ⟨0, HasDegree.zero h hE⟩
      · obtain ⟨x, y, z, hS⟩ := diophantine_descent_step_exists a b c h hE
        have hStep := hS
        obtain ⟨hTabc, -, hTxyz, r, s, t, m, -, -, -, -, -, hmc, hperm⟩ := hS
        have hzc : z < c := by
          have hzmem : z ∈ ([a, b, m] : List Nat) :=
            hperm.mem_iff.mp (by simp)
          simp at hzmem
          obtain ⟨ha0, hab, hbc, -, -, -⟩ := hTabc
          rcases hzmem with rfl | rfl | rfl
          · omega
          · omega
          · exact hmc
        obtain ⟨n, hn⟩ := ih z hzc x y hTxyz
        exact ⟨n + 1, HasDegree.succ hStep hn⟩) a b h
