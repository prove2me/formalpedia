-- Prove2me | Theorems.Thm_DetDLP_d4_unroll_guard_and_residual_bounds
-- name    : DetDLP.d4_unroll_guard_and_residual_bounds
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T09:02:02.190051+00:00
-- url     : https://prove2.me/theorems/831c063a-f53e-41fa-a94f-de01f1b7d37c
-- title:
--   Uniform guard, exact finite-ring expansion and residual size bounds
-- statement:
--   For every valid partial unroll, the root contraction, multiplied by the uniform guard power, equals the sum of padded branch coefficients times products of canonical stopped-leaf lifts. The guard is polynomial and bounds every leaf precision. The same guard satisfies the digit-rank bound, the two linear scalar query bounds, and the explicit maximum residual-degree estimate, including early stopping. This is the guarded finite-ring form of Lemma 5.3(i)-(ii).

import Definitions.Def_DetDLP_D4GuardWeight
import Definitions.Def_DetDLP_D4Plan
set_option autoImplicit false
open DetDLP DetDLP.D4Plan DetDLP.AppendixD4 DetDLP.ResidualScalarOracle DetDLP.D4GuardTree DetDLP.D3Stopped Polynomial Finset

theorem DetDLP.d4_unroll_guard_and_residual_bounds (C : ℕ) (hC : 0<C) : ∃ L₀ K : ℕ, ∀ {c : ℕ} (x : Input C c),
    let L := D3Stopped.level x.S; let D := Nat.clog 32 (4*x.m); let β := 4*x.m*x.k
    let g := totalGuard x.S D; let q := g+x.p
    L₀ ≤ L → (g:ℝ) ≤ polyBound K (D4Plan.size x) ∧
    (∀ n ≤ 4*x.m+64^D, ((digits q (digitWidth β n)^n:ℕ):ℝ) ≤ Real.exp (K*(L:ℝ)^(13/10:ℝ))) ∧
    (∀ (f : ℤ[X]) (R : Graph), f.natDegree=4*L → R.nV ≤ 4*x.m+64^D →
      precision f x.l R (digitWidth β R.nV) β ≤ K*x.b ∧ spacing f R*x.l ≤ K*x.b) ∧
    (∀ δ : ℕ, δ ≤ β/32^D+32*(L+2) ∨ (∃ M ≤ threshold x.S, δ ≤ 2*M) → δ*x.m ≤ 1217*(C+1)^3*x.b) ∧
    ∀ {f : ℤ[X]} {hf : f.Monic} {z : B f x.l x.p} (e : Expansion x.S f hf x.l 0 D x.p z),
      (∀ r, ∀ p ∈ e.leafPrec r, p ≤ q) ∧
      (∑ r, 2^(g-localAllowance x.S D*slots D)*red f x.l q (e.paddedWeight (localAllowance x.S D) r)*e.leaves q r) = 2^g*lift hf q z := by sorry
