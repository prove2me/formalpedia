-- Prove2me | Theorems.Thm_AGT_polynomial_weights_bound
-- name    : AGT.polynomial_weights_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T03:32:34.156462+00:00
-- url     : https://prove2.me/theorems/e3ede248-3e03-48fc-b716-80006a24800a
-- title:
--   The Polynomial Weights regret bound
-- statement:
--   The Polynomial Weights algorithm tracks the best single action up to an additive $\eta\, Q^T_k + \ln(N)/\eta$ (Theorem 4.6 of *Algorithmic Game Theory*). Fix $N = n+1$ actions, a learning rate $0 < \eta \le 1/2$, and any loss sequence with $\ell^t_i \in [0,1]$. The Polynomial Weights algorithm — weights start at $1$, get multiplied by $(1-\eta\,\ell^t_i)$ each step, play is the normalized weight vector — satisfies, for every horizon $T$ and every comparison action $k$,
--   $$L^T_{PW} \;\le\; L^T_k + \eta\, Q^T_k + \frac{\ln N}{\eta}, \qquad Q^T_k = \sum_{t<T}(\ell^t_k)^2 .$$
--   Tuning $\eta = \min\{\sqrt{\ln N / T}, 1/2\}$ yields external regret at most $2\sqrt{T\ln N}$, the form the capstone consumes.
--
--   *A note on the hypotheses.* The book states only $\eta \le 1/2$; strict positivity is added because at $\eta = 0$ the term $\ln N/\eta$ — infinite in intent — degenerates under total division and the inequality becomes false for $N \ge 2$. Under $0<\eta\le 1/2$ and $[0,1]$ losses every weight lies in $[(1/2)^t, 1]$, so the normalization is a genuine distribution and no degenerate case of the total division is exercised.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Section 4.3.3, Theorem 4.6, pp. 86-87

import Definitions.Def_agt_regret
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace AGT

/-- **Theorem 4.6 of *Algorithmic Game Theory***: the Polynomial Weights
algorithm with learning rate `0 < η ≤ 1/2`, on any `[0,1]`-valued loss
sequence, satisfies for every horizon `T` and every comparison action `k`
`L_PW ≤ L_k + η Q_k + ln(N)/η`, where `Q_k = ∑_{t<T} (ℓᵗ_k)²` and `N = n+1`
is the number of actions.

The book states the hypothesis as `η ≤ 1/2`; positivity of `η` is required
as well — with `η = 0` the term `ln(N)/η` is not the intended `+∞` in a
formalization with total division, and the resulting inequality is false for
`N ≥ 2`. -/
theorem polynomial_weights_bound {n : ℕ} (η : ℝ) (hη0 : 0 < η)
    (hη : η ≤ 1 / 2) (ℓ : ℕ → Fin (n + 1) → ℝ)
    (hℓ : ∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) (k : Fin (n + 1)) :
    ∑ t ∈ Finset.range T, ∑ i, pwProb η ℓ t i * ℓ t i ≤
      actionLoss ℓ k T + η * ∑ t ∈ Finset.range T, (ℓ t k) ^ 2 +
        Real.log (n + 1) / η := by
  sorry

end AGT
