-- Prove2me | Theorems.Thm_BadLocalMin_Smooth_theorem_1
-- name    : BadLocalMin.Smooth.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:05.734986+00:00
-- url     : https://prove2.me/theorems/e6656ae3-f5ce-402a-8d40-05ec214da6e6
-- title:
--   Theorem 1, p. 12 — for X under Assumption 1, σ under Assumption 2, N ≥ 3 and d_H ≥ 2, some Y gives E a sub-optimal local minimum
-- statement:
--   Consider a fully connected network with $H \ge 1$ hidden layers of widths $d_1, \dots, d_H$, input width $d_0$ and output width $d_{H+1}$, all positive, with activation $\sigma$, hidden biases and no output bias. Let $X \in \mathbb R^{d_0\times N}$ with $N \ge 3$. Suppose that $X$ satisfies Assumption 1, that $\sigma$ satisfies Assumption 2, and that the last hidden layer has at least two neurons, $d_H \ge 2$. Then there is an output matrix $Y \in \mathbb R^{d_{H+1}\times N}$ such that the empirical loss
--   $$E(\Theta) = \|Y - T_{H+1}(\Theta)\|_F^2$$
--   has a sub-optimal local minimum: a configuration $\Theta$ that is a local minimum of $E$ and a configuration $\Theta'$ with $E(\Theta') < E(\Theta)$.
--
--   The theorem says that for generic input data and almost every smooth activation, over-parameterization in depth or width does not by itself remove bad local minima of the squared loss.
--
--   **Formalization Note.** $X$ and $\sigma$ are arbitrary subject to the assumptions, and $Y$ is chosen afterwards. "Sub-optimal local minimum" follows the paper's terminology (p. 6): a local minimum that is not a global minimum. Added hypotheses, disclosed: $H \ge 1$ (the theorem speaks of "the last hidden layer") and positive widths $d_0 \ge 1$, $d_h \ge 1$ for $1 \le h \le H+1$; with a zero output width the loss is identically zero, and with a zero hidden width the output does not depend on $X$. The parameter space is the full product of all weights and biases with its usual topology.
-- source:
--   Ding, Li & Sun, arXiv:1911.01413v3, p. 12, Theorem 1; terminology p. 6, §1.4

import Mathlib
import Definitions.Def_BadLocalMin_Smooth_Model

namespace BadLocalMin.Smooth

/-- Theorem 1 (p. 12). For every input X satisfying Assumption 1 with N ≥ 3, every activation
σ satisfying Assumption 2, and d_H ≥ 2, there is an output matrix Y for which the empirical
loss E has a sub-optimal local minimum (p. 6: a local minimum that is not a global minimum).
Added (disclosed): H ≥ 1 and positive widths d₀, d₁, …, d_{H+1}. -/
theorem theorem_1 (H N : ℕ) (d : ℕ → ℕ) (σ : ℝ → ℝ) (X : Fin (d 0) → Fin N → ℝ)
    (hH : 1 ≤ H) (hd0 : 1 ≤ d 0) (hd : ∀ h, 1 ≤ h → h ≤ H + 1 → 1 ≤ d h)
    (hN : 3 ≤ N) (hA1 : Assumption1 X) (hA2 : Assumption2 σ) (hdH : 2 ≤ d H) :
    ∃ Y : Fin (d (H + 1)) → Fin N → ℝ, ∃ θ : Params d H,
      IsLocalMin (loss σ X Y) θ ∧ ∃ θ' : Params d H, loss σ X Y θ' < loss σ X Y θ := by sorry

end BadLocalMin.Smooth
