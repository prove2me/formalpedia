-- Prove2me | Theorems.Thm_CubeSampling_theorem_1_5
-- name    : CubeSampling.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:22:58.1758+00:00
-- url     : https://prove2.me/theorems/5eaa19f1-b7e9-4af0-afa0-d1e094e6a7ef
-- title:
--   Theorem 1.5 — minimax sample threshold $N_{\mathrm{par}} = (m+t)e^{\Lambda_{d,k}\pm O(k^{1/3})}$, attained by OLS
-- statement:
--   **Theorem 1.5** (minimax sample threshold). Fix $q_0 \in (0, 1/2)$ and $A \ge 16$. There is a constant $C_{q_0,A}$ such that the following holds for every noise level $\sigma > 0$ and all integers $d, k, m$ and $\delta$ with
--   $$
--   1 \le k \le q_0 d, \qquad 1 \le m \le D_{d,k}, \qquad 0 < \delta \le 1/4 .
--   $$
--   Put $t = \log(1/\delta)$. Then the parametric threshold $N_{\mathrm{par}}(d,k,m,A,\delta)$ of Definition 1.3 and the threshold $N_{\mathrm{OLS}}$ of ordinary least squares are finite, and
--
--   1. (upper bound, every feasible $m$, attained by OLS)
--   $$
--   \log\frac{N_{\mathrm{OLS}}}{m+t} - \Lambda_{d,k} \le C_{q_0,A}k^{1/3}, \qquad \log\frac{N_{\mathrm{par}}(d,k,m,A,\delta)}{m+t} - \Lambda_{d,k} \le C_{q_0,A}k^{1/3};
--   $$
--   2. (two-sided bound) if $m \le M_{d,k} \vee t$, then
--   $$
--   \Bigl|\log\frac{N_{\mathrm{par}}(d,k,m,A,\delta)}{m+t} - \Lambda_{d,k}\Bigr| \le C_{q_0,A}\,k^{1/3}.
--   $$
--
--   Here $N_{\mathrm{par}}$ is the least $N \ge 1$ with $R_{n,\delta}(d,k,m) \le A\sigma^2(m+t)/n$ for all $n \ge N$, where $R_{n,\delta}(d,k,m)$ is the worst-case minimax $(1-\delta)$-quantile risk over $m$-dimensional $V \subseteq P_{d,k}$, and $N_{\mathrm{OLS}}$ is the same threshold for the worst-case risk of ordinary least squares.
--
--   The theorem determines how many random examples are needed before the parametric rate is guaranteed for every $m$-dimensional model of degree at most $k$: $(m+t)\,e^{\Lambda_{d,k} \pm O(k^{1/3})}$, with $\Lambda_{d,k} = d\Psi(k/d)$.
--
--   Differences from the source:
--   - encoding: an m-dimensional subspace V with its orthonormal basis Φ_V → an orthonormal family Φ : Fin m → (cube → ℝ); reason: the paper notes the choice of basis is arbitrary; V = span Φ
--   - encoding: estimators with any randomness; probabilities include estimator randomness → measurable maps of the data and an independent U ~ Uniform[0,1]; reason: standard representation of randomized estimators; deterministic estimators are included
--   - encoding: Q_{1−δ}(Z) = inf{r ≥ 0 : P(Z ≤ r) ≥ 1 − δ}, inf ∅ = +∞ → infimum in [0,∞] over finite r; reason: same quantity: r is a real number in the paper
--   - encoding: N_par an integer (the least N ≥ 1 …), σ hidden in the notation → N_par, N_OLS in ℕ∞ with σ an explicit argument; the theorem asserts both are finite (= N, Nols) and one C for all σ > 0; reason: Lean's infimum of an empty set of naturals; the paper's constant does not depend on σ
--   - reading: the upper bound is attained by ordinary least squares → the threshold N_OLS of the worst-case OLS risk satisfies the same upper bound; reason: the upper bound of Step 1 (Section 6.1) is proved for OLS
--   - generalization: ordinary least squares (a least-squares minimizer) → every measurable rule equal to the least-squares solution on nonsingular designs, arbitrary on singular ones; reason: the OLS threshold is a supremum over this class, which contains every measurable least-squares minimizer, so the bound specializes to the paper's OLS
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Theorem 1.5, p.4

import Mathlib
import Definitions.Def_CubeSampling_Npar
import Definitions.Def_CubeSampling_NparOLS
import Definitions.Def_CubeSampling_dimLowDeg
import Definitions.Def_CubeSampling_Lambda
import Definitions.Def_CubeSampling_Mdk

namespace CubeSampling

/-- Theorem 1.5 (minimax sample threshold) (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Theorem 1.5, p.4): fix `q₀ ∈ (0, 1/2)` and `A ≥ 16`. For
`1 ≤ k ≤ q₀ d`, `1 ≤ m ≤ D_{d,k}` and `0 < δ ≤ 1/4`, put `t = log(1/δ)`. If `m ≤ M_{d,k} ∨ t`, then
`|log(N_par(d, k, m, A, δ)/(m + t)) − Λ_{d,k}| ≤ C_{q₀,A} k^{1/3}`. The upper bound holds for every feasible `m`
and is attained by ordinary least squares.

**Formalization Note** One `C` per `(q₀, A)`, uniform in the noise level `σ > 0` and in `d, k, m, δ`.
Both thresholds are finite (`N`, `Nols`). "Attained by OLS" is the same upper bound for the threshold
`NparOLS` of the worst-subspace risk of every measurable OLS rule. -/
theorem theorem_1_5 (q₀ : ℝ) (hq₀ : 0 < q₀) (hq₀' : q₀ < 1 / 2) (A : ℝ) (hA : 16 ≤ A) :
    ∃ C : ℝ, ∀ σ : ℝ, 0 < σ → ∀ d k m : ℕ, 1 ≤ k → (k : ℝ) ≤ q₀ * d → 1 ≤ m →
      m ≤ dimLowDeg d k → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
      ∃ N Nols : ℕ, Npar d k m A σ δ = N ∧ NparOLS d k m A σ δ = Nols ∧
        Real.log (Nols / (m + Real.log (1 / δ))) - Lambda d k ≤ C * (k : ℝ) ^ ((1 : ℝ) / 3) ∧
        Real.log (N / (m + Real.log (1 / δ))) - Lambda d k ≤ C * (k : ℝ) ^ ((1 : ℝ) / 3) ∧
        ((m : ℝ) ≤ max (Mdk d k : ℝ) (Real.log (1 / δ)) →
          |Real.log (N / (m + Real.log (1 / δ))) - Lambda d k| ≤ C * (k : ℝ) ^ ((1 : ℝ) / 3)) := by sorry

end CubeSampling
