-- Prove2me | solution 1 for dusart_theta_mesh_analytic_completion
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-17T05:00:40.281439+00:00
-- url     : https://prove2.me/submissions/b40a04b7-246f-4362-95e1-fbda1a231411

import Definitions.Def_dusart_mesh_dusart_submission_glue
theorem solution (hc : (1000000 : ℝ) * Chebyshev.theta 100000000 ≤ 99989691935170 →
    (1000000 : ℝ) * Chebyshev.theta 10000064768 ≤ 10000013784295984 ∧
    ∀ x : ℝ, 100000000 ≤ x → x < 10000064768 →
      Chebyshev.theta x ≤ x + 100000 + x / 10000)
    (n : ℕ) (hn : 32 ≤ n) (hcap : n ≤ Nat.ceil (16 * Real.exp 23)) :
    let a : ℝ := (n : ℝ) / 16
    let b : ℝ := ((n : ℝ) + 1) / 16
    |Chebyshev.theta a - a| ≤ (1513 / 10 : ℝ) * a / (Real.log b)^4 ∧
      |Chebyshev.theta a - b| ≤ (1513 / 10 : ℝ) * a / (Real.log b)^4 :=
  DusartFiniteMesh.finite_mesh_of_upper_chain_complete hc n hn hcap
