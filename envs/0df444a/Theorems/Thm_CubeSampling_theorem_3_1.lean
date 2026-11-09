-- Prove2me | Theorems.Thm_CubeSampling_theorem_3_1
-- name    : CubeSampling.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:18:50.186327+00:00
-- url     : https://prove2.me/theorems/5db2b2b6-ee22-4719-9652-602bf9fec8a1
-- title:
--   Theorem 3.1 — Kirshner–Samorodnitsky moment bound
-- statement:
--   **Theorem 3.1** (Kirshner–Samorodnitsky, [KS21, Corollary 1.4]). Let $p \ge 2$, let $d, k$ be integers with $0 \le k \le d/2$, and let $f \in P_{d,k}$ be nonzero. Then
--   $$
--   \frac{\mathbb E[|f|^p]}{(\mathbb E[f^2])^{p/2}} \le \exp\bigl(d\,F(p, k/d)\bigr),
--   $$
--   with $F$ the rate defined in (6) (including the endpoint values $F(p,0) = 0$, $F(p,1/2) = (p/2-1)\log 2$).
--
--   This sharp moment bound is the analytic input of the clipping estimate (Proposition 3.3) and hence of the upper bound in Theorem 1.5.
--
--   Differences from the source:
--   - encoding: z the unique root of the equation in (6) → z chosen by Classical.epsilon among the roots; reason: the paper asserts uniqueness, so the value is the paper's; existence is proved in the sanity file
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Theorem 3.1, p.13

import Mathlib
import Definitions.Def_CubeSampling_lowDeg
import Definitions.Def_CubeSampling_cubeMean
import Definitions.Def_CubeSampling_ksF

namespace CubeSampling

/-- Theorem 3.1 (Kirshner–Samorodnitsky, [KS21, Corollary 1.4]) (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Theorem 3.1, p.13):
for `p ≥ 2`, `0 ≤ k ≤ d/2` and nonzero `f ∈ P_{d,k}`, `E[|f|^p] / (E[f²])^{p/2} ≤ exp(d F(p, k/d))`, with `F`
the rate (6). -/
theorem theorem_3_1 (p : ℝ) (hp : 2 ≤ p) (d k : ℕ) (hk : (k : ℝ) ≤ (d : ℝ) / 2)
    (f : Cube d → ℝ) (hf : f ∈ lowDeg d k) (hf0 : f ≠ 0) :
    cubeMean d (fun x => |f x| ^ p) / (cubeMean d (fun x => f x ^ 2)) ^ (p / 2) ≤
      Real.exp (d * ksF p ((k : ℝ) / d)) := by sorry

end CubeSampling
