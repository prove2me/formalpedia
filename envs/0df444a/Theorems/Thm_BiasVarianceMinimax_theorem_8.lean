-- Prove2me | Theorems.Thm_BiasVarianceMinimax_theorem_8
-- name    : BiasVarianceMinimax.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:34:16.271946+00:00
-- url     : https://prove2.me/theorems/efcc4f26-1e8c-4225-a252-3201e0fa9506
-- title:
--   Theorem 8 — the AMRR of weighted estimators is $\frac{q_1}{q_1+q_2}\frac1{K^{2q_2}}$, attained by two-decay weights
-- statement:
--   Let $q_1,q_2,K>0$, $n_0\in\mathbb N$ and $\alpha=1/(2(q_1+q_2))$.
--
--   **Part 1.** The asymptotic minimax risk ratio of the weighted estimators against the sample average is
--
--   $$\min_{g(\cdot)\in\mathcal F_K,\ W\in\mathcal W}\ \max_{\hat\theta(\cdot)\in\Theta,\ d>0}R^{gen}(\hat\theta(\cdot),d,g(d),W)=\frac{q_1}{q_1+q_2}\,\frac1{K^{2q_2}}.$$
--
--   **Part 2.** For all large $n$, problem (24) has an optimal solution. For any choice of optimal solutions $a^*=a_n$, the calibration $g(d)=Kd$, which lies in $\mathcal F_K$, and the weights
--
--   $$w^*_{j,n}=\frac{\lambda_1^*}{(j+n_0)^{(q_1+2q_2)/(2(q_1+q_2))}}+\frac{\lambda_2^*}{(j+n_0)^{q_2/(q_1+q_2)}},\qquad\begin{bmatrix}\lambda_1^*\\ \lambda_2^*\end{bmatrix}=\begin{bmatrix}\xi_{11}&\xi_{12}\\ \xi_{21}&\xi_{22}\end{bmatrix}\begin{bmatrix}a^*\\ 1\end{bmatrix}$$
--
--   achieve this value. Moreover, the risk ratio at this configuration equals the value for every model in $\Theta$ and every $d>0$.
--
--   The theorem says how much a weighted estimator can gain against the sample average when $B$ and $\sigma^2$ are unknown: for $q_1=2$, $q_2=1$, $K=1$ the value is $2/3$. It also gives the form of the best weights, a sum of two components with distinct decay rates.
--
--   **Formalization Note** The minimum is `IsLeast`, so it is attained. `W∗` is not claimed to be the only array attaining it.
--
--   Differences from the source:
--   - reading: inner max over θ̂(·) and d → a supremum in ℝ≥0∞; reason: for a general W the max need not be attained; the end of p.60 proves the supremum form
--   - reading: σ²(δ) = Var(ε(δ)) with only its limit stated → finite variance at every δ > 0, a field of the class; reason: σ²(δ) is printed as a real function and a run at any positive δ can occur
--   - reading: a∗ an optimal solution to (24), with the weights "given by" it for all n → (24) is solvable for all large n, and every selection optimal for all large n is covered; reason: (24) can be empty at finite n and Ξ is singular at n = 1, and the limsup does not read small n
--   - encoding: θ̂(δ) a random variable with independent runs → a law per δ > 0, with runs as coordinates under `Measure.pi` over `Fin n`; reason: the mean squared errors depend only on the laws; same class
--   - encoding: n₀ any fixed integer → n₀ ∈ ℕ; reason: a negative n₀ makes j + n₀ ≤ 0 at j = 1, where δⱼ is undefined
--   - encoding: g(d) ≤ Kd → 0 < g(d) ≤ Kd for d > 0; reason: g maps ℝ₊ to ℝ₊ by p.13, and δⱼ > 0
--   - encoding: R^gen a real limsup, min over (g, W) → values in ℝ≥0∞, min as `IsLeast`; reason: the ratio can be unbounded, and `IsLeast` keeps attainment
--   - generalization: W∗ and g achieve (22) → additionally R^gen = the value for every model and every d > 0; reason: stronger than the max form, which follows by taking the supremum
-- source:
--   Lam, Zhang & Zhang, arXiv:1902.04673v1, Theorem 8, pp.20–21; proof Appendix C, pp.50–60

import Mathlib
import Definitions.Def_BiasVarianceMinimax_gameValue
import Definitions.Def_BiasVarianceMinimax_IsOptimal
import Definitions.Def_BiasVarianceMinimax_weightStar

open Filter
open scoped ENNReal

namespace BiasVarianceMinimax

/-- **Theorem 8** (the AMRR of general weighted estimators and its optimal calibration).
Lam, Zhang & Zhang, arXiv:1902.04673v1, Theorem 8, pp.20–21; proof Appendix C, pp.50–60.

For `q₁, q₂, K > 0` and `n₀ ∈ ℕ`:
1. (22): `(q₁/(q₁+q₂))(1/K^(2q₂))` is the least value of
   `max_{θ̂(·)∈Θ, d>0} R^gen(θ̂(·), d, g(d), W)` over `g ∈ 𝓕_K` and triangular arrays `W`.
2. Problem (24) has an optimal solution for all large `n`, and for every choice `a` of such solutions
   the calibration `g(d) = K d`, which lies in `𝓕_K`, and the weights `W∗(a)` of (23) achieve (22).
   Moreover the risk ratio at `(g, W∗(a))` equals that number for every model and every `d > 0`.

**Formalization Note.** `min` over `(g, W)` is `IsLeast`, so it is attained. The inner `max` is a
supremum in `ℝ≥0∞`: for a general `W` it need not be attained, while the last clause shows it is
attained at `W∗(a)`, by every model. (24) can be infeasible at finite `n` and `Ξ` is junk at `n = 1`,
so the solvability and the optimality of `a` are for all large `n`, and `W∗` at small `n` is not
read by the `limsup`. `W∗` is not unique, and no uniqueness is claimed. -/
theorem theorem_8 (q₁ q₂ K : ℝ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hK : 0 < K) (n₀ : ℕ) :
    IsLeast {v : ℝ≥0∞ | ∃ g ∈ calibrationClass K, ∃ W : TriangularArray,
        v = gameValue q₁ q₂ n₀ g W}
      (ENNReal.ofReal (q₁ / (q₁ + q₂) * (1 / K ^ (2 * q₂)))) ∧
    (∀ᶠ n in atTop, ∃ a : ℝ, IsOptimal q₁ q₂ K n₀ n a) ∧
    ∀ a : ℕ → ℝ, (∀ᶠ n in atTop, IsOptimal q₁ q₂ K n₀ n (a n)) →
      (fun d : ℝ => K * d) ∈ calibrationClass K ∧
      gameValue q₁ q₂ n₀ (fun d : ℝ => K * d) (weightStar q₁ q₂ n₀ a) =
        ENNReal.ofReal (q₁ / (q₁ + q₂) * (1 / K ^ (2 * q₂))) ∧
      ∀ (M : SimulationOutput q₁ q₂) (d : ℝ), 0 < d →
        riskRatio M n₀ d (K * d) (weightStar q₁ q₂ n₀ a) =
          ENNReal.ofReal (q₁ / (q₁ + q₂) * (1 / K ^ (2 * q₂))) := by sorry

end BiasVarianceMinimax
