-- Prove2me | Theorems.Thm_BiasVarianceMinimax_risk_ratio_at_optimal_weights
-- name    : BiasVarianceMinimax.risk_ratio_at_optimal_weights
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:34:36.03963+00:00
-- url     : https://prove2.me/theorems/c1955a3e-4c79-4cf4-977c-da9931c4f60e
-- title:
--   p.51, pp.56–57 — the value at $W^*$
-- statement:
--   Let $a_n$ be optimal for (24) for all large $n$. For every $\hat\theta(\cdot)\in\Theta$ and every $d>0$, with $\tilde d=Kd$,
--
--   $$\frac{\mathrm{MSE}_1^{gen}(\hat\theta(\cdot),Kd,W^*(a))}{\mathrm{MSE}_0(\hat\theta(\cdot),d)}\ \longrightarrow\ \frac{q_1}{q_1+q_2}\,\frac1{K^{2q_2}}\qquad(n\to\infty),$$
--
--   and hence $R^{gen}(\hat\theta(\cdot),d,Kd,W^*(a))$ equals this number. This is the upper half of Theorem 8: the ratio is the same for every model and every $d$.
--
--   Differences from the source:
--   - reading: g(d) = η∗d with the remark that substituting η with its limit does not affect the ratio → g(d) = Kd; reason: this is the calibration of Theorem 8, and η∗ → K
--   - generalization: max over θ̂(·) and d of R^gen equals lim n^(q₁/(q₁+q₂)) Sₙ∗ → the ratio converges to that number for each model and each d; reason: stronger than the max form, which follows by taking the supremum
--   - generalization: Appendix C assumes n₀ = 0 → the statement holds for every n₀ ∈ ℕ; reason: specializes to the page at n₀ = 0; Theorem 8 needs n₀
--   - reading: σ²(δ) = Var(ε(δ)) with only its limit stated → finite variance at every δ > 0, a field of the class; reason: σ²(δ) is printed as a real function and a run at any positive δ can occur
-- source:
--   Lam, Zhang & Zhang, arXiv:1902.04673v1, p.51; pp.56–57

import Mathlib
import Definitions.Def_BiasVarianceMinimax_IsOptimal
import Definitions.Def_BiasVarianceMinimax_weightStar

open Filter Topology

namespace BiasVarianceMinimax

/-- **The value at `W∗`.** Lam, Zhang & Zhang, arXiv:1902.04673v1, p.51, with the argument of
pp.56–57.

For `a` optimal for large `n`, every model of `Θ` and every `d > 0`: at `W∗(a)` and `d̃ = K d` the
ratio `MSE₁/MSE₀` converges to `(q₁/(q₁+q₂))(1/K^(2q₂))`, so the risk ratio equals that number.

**Formalization Note.** The page has `g(d) = η∗ d` and passes to the limit `K` (p.51, "substituting
`η` with its limit will not affect the asymptotic risk ratio"); Theorem 8 has `g(d) = K d`, which is
stated here. By `limit_76_77_80` the number is `lim n^(q₁/(q₁+q₂)) Sₙ∗`. -/
theorem risk_ratio_at_optimal_weights (q₁ q₂ K : ℝ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hK : 0 < K)
    (n₀ : ℕ) (a : ℕ → ℝ) (ha : ∀ᶠ n in atTop, IsOptimal q₁ q₂ K n₀ n (a n))
    (M : SimulationOutput q₁ q₂) (d : ℝ) (hd : 0 < d) :
    Tendsto (fun n : ℕ =>
        mseWeighted M n₀ (K * d) n (weightStar q₁ q₂ n₀ a n) / mseBaseline M n₀ d n) atTop
      (𝓝 (q₁ / (q₁ + q₂) * (1 / K ^ (2 * q₂)))) ∧
    riskRatio M n₀ d (K * d) (weightStar q₁ q₂ n₀ a) =
      ENNReal.ofReal (q₁ / (q₁ + q₂) * (1 / K ^ (2 * q₂))) := by sorry

end BiasVarianceMinimax
