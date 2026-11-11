-- Prove2me | Theorems.Thm_ApproxSyzygies_Smoothed_lemma_a_2
-- name    : ApproxSyzygies.Smoothed.lemma_a_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:02:10.606972+00:00
-- url     : https://prove2.me/theorems/bb515ffe-f07d-4ad3-bb8c-5f32df7c68cf
-- title:
--   Lemma A.2 — Gaussian norm bound: $\Pr[\|X-\mu\|>2\rho\sqrt{N+t}]\le e^{-N/2-t}$
-- statement:
--   Let $N\ge1$, $\rho>0$, $\mu\in\mathbb R^N$ and $X\sim N(\mu,\rho^2I_N)$. For every $t\ge0$,
--   $$\Pr\big[\|X-\mu\|>2\rho\sqrt{N+t}\big]\le e^{-N/2-t},$$
--   and in particular (taking $t=0$) $\Pr[\|X-\mu\|>2\rho\sqrt N]\le e^{-N/2}$. In the proof of Theorem 4.1 it bounds the size of the Gaussian perturbations, hence $\|b\|$ and $\|\tilde b\|$.
--
--   Differences from the source:
--   - encoding: $X\sim N(\mu,\rho^2I_N)$ → the law `Measure.pi fun j => gaussianReal (μ j) (ρ^2)` of $X$, and the Euclidean norm of $x-\mu$; reason: the probability of an event about $X$ is the law's measure of it
-- source:
--   Bhaskara, Guo, Sinha, Srinivas, Vijayaraghavan, Approximate Syzygies of Smoothed Polynomials and Applications, STOC 2027 submission (manuscript sha256 9c17d04e…), p. 85, Lemma A.2

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ApproxSyzygies.Smoothed

/-- Lemma A.2 (p. 85): for `N ≥ 1`, `ρ > 0`, `μ ∈ ℝ^N` and `X ∼ N(μ, ρ² I_N)`,
`P[‖X − μ‖ > 2ρ√(N + t)] ≤ e^{−N/2−t}` for every `t ≥ 0`; in particular
`P[‖X − μ‖ > 2ρ√N] ≤ e^{−N/2}`. The law of `X` is the product of the `N(μ_j, ρ²)`. -/
theorem lemma_a_2 (N : ℕ) (hN : 1 ≤ N) (ρ : ℝ) (hρ : 0 < ρ) (μ : Fin N → ℝ) :
    (∀ t : ℝ, 0 ≤ t →
      (Measure.pi fun j : Fin N => gaussianReal (μ j) (ρ ^ 2).toNNReal)
          {x | 2 * ρ * Real.sqrt (N + t) < ‖(WithLp.toLp 2 (x - μ) : EuclideanSpace ℝ (Fin N))‖}
        ≤ ENNReal.ofReal (Real.exp (-(N : ℝ) / 2 - t))) ∧
    (Measure.pi fun j : Fin N => gaussianReal (μ j) (ρ ^ 2).toNNReal)
        {x | 2 * ρ * Real.sqrt N < ‖(WithLp.toLp 2 (x - μ) : EuclideanSpace ℝ (Fin N))‖}
      ≤ ENNReal.ofReal (Real.exp (-(N : ℝ) / 2)) := by sorry

end ApproxSyzygies.Smoothed
