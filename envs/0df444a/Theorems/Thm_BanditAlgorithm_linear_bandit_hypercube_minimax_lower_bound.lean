-- Prove2me | Theorems.Thm_BanditAlgorithm_linear_bandit_hypercube_minimax_lower_bound
-- name    : BanditAlgorithm.linear_bandit_hypercube_minimax_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-29T16:53:15.271972+00:00
-- url     : https://prove2.me/theorems/2fd3bcd5-1e26-4790-ac83-1dffea9c084a
-- statement:
--   (Hypercube lower bound, L&S Theorem 24.1) Let $\mathcal{A} = [-1,1]^d$ and $\Theta = \{-n^{-1/2}, n^{-1/2}\}^d$, with unit-variance Gaussian noise $X_t = \langle A_t,\theta\rangle + \eta_t$, $\eta_t \sim \mathcal{N}(0,1)$. Then, for any policy supported in $\mathcal{A}$, there exists $\theta \in \Theta$ such that
--
--   $$R_n(\mathcal{A},\theta) \ge \frac{e^{-2}}{8}\, d\sqrt{n}.$$
--
--   (The book states no further conditions; $d \ge 1$, $n \ge 1$ are the chapter's standing assumptions.)
-- source:
--   L&S Theorem 24.1, p.289

import Definitions.Def_LinearBanditProtocol


open Matrix MeasureTheory

theorem BanditAlgorithm.linear_bandit_hypercube_minimax_lower_bound {d n : ℕ}
    (hd : 0 < d) (hn : 0 < n) (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy {a : Fin d → ℝ | ∀ i, |a i| ≤ 1} π) :
    ∃ θ : Fin d → ℝ,
      (∀ i, θ i = Real.sqrt (1 / n) ∨ θ i = -Real.sqrt (1 / n)) ∧
      Real.exp (-2) / 8 * (d * Real.sqrt n) ≤
        linearBanditExpectedRegret {a : Fin d → ℝ | ∀ i, |a i| ≤ 1} θ π n := by
  sorry
