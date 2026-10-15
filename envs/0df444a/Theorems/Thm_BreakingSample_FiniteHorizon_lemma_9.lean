-- Prove2me | Theorems.Thm_BreakingSample_FiniteHorizon_lemma_9
-- name    : BreakingSample.FiniteHorizon.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:44.91798+00:00
-- url     : https://prove2.me/theorems/abb1bd75-b2e3-40d4-ae0e-c2b5339cfbe3
-- title:
--   Lemma 9, p. 21 — under the Bernstein-type condition (63) and N > 12Hβ₁, ‖V̂^(0)_h − V^(0)_h‖∞ ≤ 6H√(3β₁H/N)
-- statement:
--   Let $(\{P_h\},\{r_h\})$ be a finite-horizon MDP with horizon $H$ and rewards in $[0,1]$, let $\{\widehat P_h\}$ be another family of transition kernels on the same spaces, let $\pi$ be a deterministic nonstationary policy and let $N$ be a positive integer. Let $V^{(l)}_h$ be the auxiliary vectors (62) built from the true kernels, and $\widehat V^{(0)}_h$ the value of $\pi$ under $\{\widehat P_h\}$, so that $V^{(0)}_h=V^\pi_h$ and $\widehat V^{(0)}_h=\widehat V^\pi_h$.
--
--   Suppose there is $\beta_1>0$ such that, for all integers $0\le l\le\log_2H$ and all $1\le h\le H-1$, entrywise in $s$,
--   $$\Big|\big(\widehat P_{h,\pi}-P_{h,\pi}\big)V^{(l)}_{h+1}\Big|\le\sqrt{\frac{\beta_1}{N}}\sqrt{\mathrm{Var}_{P_{h,\pi}}\big[V^{(l)}_{h+1}\big]}+\frac{\beta_1\|V^{(l)}_{h+1}\|_\infty}{N}\mathbf 1.\tag{63}$$
--   If in addition $N>12H\beta_1$, then for all $1\le h\le H$,
--   $$\big\|\widehat V^{(0)}_h-V^{(0)}_h\big\|_\infty\le6H\sqrt{\frac{3\beta_1H}{N}}.$$
--
--   This deterministic lemma turns Bernstein-type concentration of the one-step errors into a bound on the error of the plug-in value; it is applied to the optimal policy and to the planner's policy in the proof of Theorem 4.
--
--   **Formalization Note** The paper states the lemma for the empirical kernels (6); here $\widehat P_h$ is any family of transition kernels, which contains that case. Steps are 0-based: the paper's range $1\le h\le H-1$ is `h.val + 1 < H`. The index $l$ is a natural number with $l\le\log_2 H$ as reals.
-- source:
--   arXiv:2005.12900v8, §7.2, Lemma 9, (63)–(64), p. 21

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_BreakingSample_FiniteHorizon_Model

namespace BreakingSample.FiniteHorizon

open FoundationsML.ReinforcementLearning

/-- Lemma 9 (arXiv:2005.12900v8, §7.2, (63)–(64), p. 21). `Phat` is any family of transition kernels (the
empirical kernels of (6) are one). If the auxiliary vectors `V⁽ˡ⁾_{h+1}` of (62) for the policy `π` satisfy the
Bernstein-type condition (63) with some `β₁ > 0` for all `0 ≤ l ≤ log₂ H` and all paper steps
`1 ≤ h ≤ H − 1` (Lean: `h.val + 1 < H`), and `N > 12Hβ₁`, then `‖V̂⁽⁰⁾_h − V⁽⁰⁾_h‖∞ ≤ 6H√(3β₁H/N)` at every
step, where `V⁽⁰⁾ = V^π` and `V̂⁽⁰⁾ = V̂^π`. -/
theorem lemma_9 {S A : Type} [Fintype S] {H N : ℕ}
    (P Phat : Fin H → S → A → S → ℝ) (r : Fin H → S → A → ℝ) (hM : IsFHMDP P r)
    (hPhat : ∀ h, IsTransitionKernel (Phat h)) (π : Fin H → S → A) (β₁ : ℝ) (hβ₁ : 0 < β₁)
    (h63 : ∀ l : ℕ, (l : ℝ) ≤ Real.logb 2 H → ∀ h : Fin H, h.val + 1 < H → ∀ s : S,
      |∑ s', (Phat h s (π h s) s' - P h s (π h s) s') *
          propagate P π (auxReward P r π l) (h.val + 1) s'| ≤
        Real.sqrt (β₁ / N) *
            Real.sqrt (varStep P π h (propagate P π (auxReward P r π l) (h.val + 1)) s) +
          β₁ * ‖propagate P π (auxReward P r π l) (h.val + 1)‖ / N)
    (hN : 12 * (H : ℝ) * β₁ < N) :
    ∀ h : Fin H,
      ‖value Phat r π h.val - value P r π h.val‖ ≤ 6 * H * Real.sqrt (3 * β₁ * H / N) := by sorry

end BreakingSample.FiniteHorizon
