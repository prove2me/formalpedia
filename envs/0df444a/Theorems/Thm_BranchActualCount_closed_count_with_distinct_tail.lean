-- Prove2me | Theorems.Thm_BranchActualCount_closed_count_with_distinct_tail
-- name    : BranchActualCount.closed_count_with_distinct_tail
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-17T12:42:16.588195+00:00
-- url     : https://prove2.me/theorems/ae5a6ecb-4c39-40c4-8cbf-9c5d10ca20c9
-- title:
--   Closed zeta zero count plus a distinct certified tail
-- statement:
--   Let N(H) count the zeta zeros with 0<Im(s)<H and let Nc(T) count those with 0<Im(s)≤T, both with multiplicities. For 0≤T<H and any list L of pairwise distinct zeta zeros with T<Im(s)<H, Nc(T)+|L|≤N(H). The zeros in L need not be assumed simple.
-- source:
--   Underlying xi/zeta analytic facts from Mathlib; functional-equation proof adapted from smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033, Apache-2.0 attribution preserved. Weighted closed-cut/tail comparison formalized by Desenvolvimento RH, coordinated by Ricardo Marangoni Brandão Bueno.

import Mathlib

theorem BranchActualCount.closed_count_with_distinct_tail :
  let N : ℝ → ℝ := fun H =>
    ∑' z : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioo 0 H ∧ s ∈ {w : ℂ | riemannZeta w=0}} : Set ℂ),
      (((meromorphicOrderAt riemannZeta (z : ℂ)).untopD 0 : ℤ) : ℝ)
  let Nc : ℝ → ℝ := fun T =>
    ∑' z : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioc 0 T ∧ s ∈ {w : ℂ | riemannZeta w=0}} : Set ℂ),
      (((meromorphicOrderAt riemannZeta (z : ℂ)).untopD 0 : ℤ) : ℝ)
  ∀ T H : ℝ, 0 ≤ T → T < H → ∀ L : List ℂ, L.Nodup →
    (∀ s ∈ L, T < s.im ∧ s.im < H ∧ riemannZeta s=0) →
    Nc T + (L.length : ℝ) ≤ N H := by sorry
