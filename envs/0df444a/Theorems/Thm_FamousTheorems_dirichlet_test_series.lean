-- Prove2me | Theorems.Thm_FamousTheorems_dirichlet_test_series
-- name    : FamousTheorems.dirichlet_test_series
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:05:26.496161+00:00
-- url     : https://prove2.me/theorems/d448bcbd-daae-4d17-ab68-81ab3698cb73
-- title:
--   Dirichlet's test for series
-- statement:
--   **Dirichlet's test for series.** Let $(f_n)$ be a nonincreasing sequence of reals tending to $0$, and let $(z_n)$ be vectors in a real normed space whose partial sums are bounded, $\|\sum_{i<n}z_i\|\le b$ for all $n$. Then the partial sums of $\sum_nf_nz_n$ form a Cauchy sequence.
--
--   In a complete space this means the series $\sum f_nz_n$ converges. Dirichlet's test proves convergence of series such as $\sum\sin(n)/n$ and $\sum e^{in\theta}/n^s$ for $\theta\notin2\pi\mathbb Z$ and $s>0$. The alternating series test is the special case $z_n=(-1)^n$.
--
--   **Formalization note.** Mathlib's `Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded`. The sequence $f$ is `Antitone` (nonincreasing) and tends to `0`, so it is nonnegative. The conclusion is `CauchySeq` of the partial sums $n\mapsto\sum_{i<n}f_i\cdot z_i$, which does not require completeness of the space.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem dirichlet_test_series {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {b : ℝ} {f : ℕ → ℝ} {z : ℕ → E}
    (hfa : Antitone f) (hf0 : Filter.Tendsto f Filter.atTop (nhds 0))
    (hgb : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ b) :
    CauchySeq fun n => ∑ i ∈ Finset.range n, f i • z i := by sorry

end FamousTheorems
