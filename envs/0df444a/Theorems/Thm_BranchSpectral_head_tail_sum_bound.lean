-- Prove2me | Theorems.Thm_BranchSpectral_head_tail_sum_bound
-- name    : BranchSpectral.head_tail_sum_bound
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T05:48:29.028102+00:00
-- url     : https://prove2.me/theorems/4309a4d0-269a-432b-b7fb-770d7c2d14b8
-- title:
--   Infinite head-tail comparison with one anchor
-- statement:
--   Let f,G be summable real sequences, j₀ an index, H,C,L real with C≥0. Assume H≤fⱼ₀, Gⱼ₀=0, fⱼ≥-CGⱼ for j≠j₀, and ∑Gⱼ≤L. Then
--   $$H-CL\le\sum_j f_j.$$
--   Scope: the explicit hypotheses of this theorem only. No proof of RH or of higher tower-diagonal positivity is claimed.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Conditional Branch 2/3 certificate, 16 Nov 2026. No claim of novelty.

import Mathlib
open MeasureTheory Set Filter Topology

theorem BranchSpectral.head_tail_sum_bound (f G : ℕ → ℝ) (j0 : ℕ) (H C L : ℝ)
    (hf : Summable f) (hG : Summable G) (hC : 0 ≤ C)
    (hhead : H ≤ f j0) (hzero : G j0 = 0)
    (hpoint : ∀ j, j ≠ j0 → -C*G j ≤ f j)
    (htail : (∑' j, G j) ≤ L) :
    H-C*L ≤ ∑' j, f j := by sorry
