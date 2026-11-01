-- Prove2me | Theorems.Thm_BiasVarianceMinimax_no_better_configuration
-- name    : BiasVarianceMinimax.no_better_configuration
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:32:45.491119+00:00
-- url     : https://prove2.me/theorems/5c2a9e54-979c-4385-aa62-df763ac90241
-- title:
--   pp.58–60 — no configuration beats the value
-- statement:
--   For every array $W$, every $d>0$ and every $\tilde d$ with $0<\tilde d\le Kd$,
--
--   $$\sup_{\hat\theta(\cdot)\in\Theta}R^{gen}(\hat\theta(\cdot),d,\tilde d,W)\ \ge\ \frac{q_1}{q_1+q_2}\,\frac1{K^{2q_2}}.$$
--
--   Taking $\tilde d=g(d)$ gives the lower half of Theorem 8.
--
--   **Formalization Note** The bound is on a supremum. The page's "We aim to find $\hat\theta(\cdot)\in\Theta$ and $d>0$" is not stated as the existence of one model: the end of p.60 takes $B$ arbitrarily close to $0$.
--
--   Differences from the source:
--   - reading: max over θ̂(·) and d, and "We aim to find θ̂(·) ∈ Θ and d > 0" → a supremum over Θ; reason: for some arrays no single model reaches the bound, and p.60 lets B tend to 0
--   - generalization: max over θ̂(·) and d, for ∑ⱼ wⱼ → 1, n₀ = 0 → for each fixed d, every array, every n₀; reason: implies the page's bound; arrays with other sums have value ⊤
-- source:
--   Lam, Zhang & Zhang, arXiv:1902.04673v1, pp.58–60

import Mathlib
import Definitions.Def_BiasVarianceMinimax_riskRatio

open scoped ENNReal

namespace BiasVarianceMinimax

/-- **No other configuration does better.** Lam, Zhang & Zhang, arXiv:1902.04673v1, pp.58–60:
`max_{θ̂(·)∈Θ, d>0} R^gen(θ̂(·), d, g(d), W) ≥ (q₁/(q₁+q₂))(1/K^(2q₂))`, in the fixed-`d` form that the
proof gives.

For every array `W`, every `d > 0` and every `0 < d̃ ≤ K d`, the supremum of the risk ratio over `Θ`
is at least `(q₁/(q₁+q₂))(1/K^(2q₂))`.

**Formalization Note.** `W` and `d̃` are chosen first and the supremum is taken after them. It is a
supremum, reached by letting `B → 0` (p.60): for some arrays no single model reaches the bound. The
form covers arrays whose sums do not tend to `1` too, whose risk is `⊤` by `weights_sum_to_one`. -/
theorem no_better_configuration (q₁ q₂ K : ℝ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hK : 0 < K) (n₀ : ℕ)
    (W : TriangularArray) (d dTilde : ℝ) (hd : 0 < d) (hdTilde : 0 < dTilde)
    (hle : dTilde ≤ K * d) :
    ENNReal.ofReal (q₁ / (q₁ + q₂) * (1 / K ^ (2 * q₂))) ≤
      ⨆ M : SimulationOutput q₁ q₂, riskRatio M n₀ d dTilde W := by sorry

end BiasVarianceMinimax
