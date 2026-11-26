-- Prove2me | Theorems.Thm_BranchActualQ_negative_seed_excluded_in_both_branches
-- name    : BranchActualQ.negative_seed_excluded_in_both_branches
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-20T10:54:52.59193+00:00
-- url     : https://prove2.me/theorems/95f92065-ece1-477e-a42c-d631025f62bc
-- title:
--   Exclusion of a negative seed in the finite and infinite off-critical zero cases
-- statement:
--   Let $S$ denote the existence of an integer $n\ge1$ and a real $u>0$ for which $Q_n(u)<0$, for the original xi-derived tower. Let $O$ denote the set of nontrivial zeros of the Riemann zeta function outside the critical line. The finite nonempty case for $O$ and the infinite case for $O$ are both incompatible with $S$.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandão Bueno. Finite and infinite off-critical zero cases for the original xi-based tower.

import Mathlib

theorem BranchActualQ.negative_seed_excluded_in_both_branches :
    let f : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let G : ℝ → ℝ := fun x => (f (1/2+(Real.sqrt x : ℂ))).re
    let Q : ℕ → ℝ → ℝ := fun n u =>
      (2 : ℝ)^n*u^(2*n-1)*(-1 : ℝ)^(n-1)*
        iteratedDeriv n (fun x => Real.log (G x)-Real.log (G 0)) (u^2)
    let S : Prop := ∃ (n : ℕ), 1 ≤ n ∧ ∃ u > 0, Q n u < 0
    let O : Set ℂ := {s | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1/2}
    (S → O.Finite → O.Nonempty → False) ∧ (S → O.Infinite → False) := by sorry
