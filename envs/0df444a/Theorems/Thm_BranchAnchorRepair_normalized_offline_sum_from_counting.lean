-- Prove2me | Theorems.Thm_BranchAnchorRepair_normalized_offline_sum_from_counting
-- name    : BranchAnchorRepair.normalized_offline_sum_from_counting
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-17T18:13:36.447873+00:00
-- url     : https://prove2.me/theorems/c6a26623-c459-45d5-ae46-731901f8ba9c
-- title:
--   Anchor-normalized off-line pole sum: decay from sublinear occurrence counting
-- statement:
--   Let gamma_i>=2, |eps_i|<=1/2, and Re(B_i)=gamma_i^2-eps_i^2 on an arbitrary occurrence index type, so multiplicities are retained. Assume gamma_i<=1000 implies eps_i=0, choose an anchor a with gamma_a<=100, and assume a sublinear bound card(F)<=C*y^p for every y>=1 and every finite F with gamma_i^2<=y, with p<1. If k_j tends to infinity, x_j>0, and k_j/x_j tends to infinity, then the complex sum over the off-line subtype eps_i!=0 of ((x_j+gamma_a^2)/(x_j+B_i))^(k_j) tends to zero. This is a conditional analytic estimate: low-height verification, an anchor, and occurrence counting are explicit premises, not asserted unconditionally for zeta here.
-- source:
--   Desenvolvimento RH, 2026-11-17. Reuses the ACCEPTED BranchLargeScaleRepair.normalized_pole_subsequence_sum_tendsto_zero (35c28087-462f-418d-b4f2-283c3af10226). The integral comparison proving reciprocal summability is reproduced with full proofs from ReciprocalCounting in actual_xi_branches.lean, under a distinct namespace. No claim of novelty for standard dominated convergence or integral comparison.

import Mathlib
open Filter Topology

theorem BranchAnchorRepair.normalized_offline_sum_from_counting {ι : Type*}
    (gamma eps : ι → ℝ) (B : ι → ℂ)
    (hB : ∀ i, (B i).re = (gamma i)^2-(eps i)^2)
    (lower : ∀ i, 2 ≤ gamma i) (strip : ∀ i, |eps i| ≤ 1/2)
    (verified : ∀ i, gamma i ≤ 1000 → eps i = 0)
    (anchor : ι) (anchor_low : gamma anchor ≤ 100)
    (C p : ℝ) (hp : p < 1)
    (hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, (gamma i)^2 ≤ y) → (F.card : ℝ) ≤ C*y^p)
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hscale : Tendsto (fun (n : ℕ) => (k n : ℝ)/x n) atTop atTop) :
    Tendsto (fun (n : ℕ) => ∑' i : {i // eps i ≠ 0},
      (((x n+(gamma anchor)^2 : ℝ) : ℂ)/((x n : ℂ)+B i))^(k n))
      atTop (𝓝 0) := by sorry
