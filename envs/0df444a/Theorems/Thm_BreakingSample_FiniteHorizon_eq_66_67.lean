-- Prove2me | Theorems.Thm_BreakingSample_FiniteHorizon_eq_66_67
-- name    : BreakingSample.FiniteHorizon.eq_66_67
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:42.686952+00:00
-- url     : https://prove2.me/theorems/bb55e975-0e3e-4ac9-a88a-72fb10280394
-- title:
--   (66)–(67), p. 21 — for a fixed policy, the Bernstein-type bound on (P̂_h − P_h)V^(l)_{h+1} holds w.p. ≥ 1 − δ with β₁ = 4log(H|S||A|/δ)
-- statement:
--   Let $(\{P_h\},\{r_h\})$ be a finite-horizon MDP on finite spaces $\mathcal S,\mathcal A$ with horizon $H$ and rewards in $[0,1]$, let $\pi$ be a deterministic nonstationary policy that does not depend on the data, let $\delta>0$, and draw $N\ge1$ independent samples $s^i_h(s,a)\sim P_h(\cdot\mid s,a)$ for every triple $(s,a,h)$, with empirical kernels $\widehat P_h$ as in (6). Let $V^{(l)}_h$ be the auxiliary vectors (62) of $\pi$ and set
--   $$\beta_1=4\log\Big(\frac{H|\mathcal S||\mathcal A|}{\delta}\Big).\tag{67}$$
--   Then with probability at least $1-\delta$, uniformly over all integers $0\le l\le\log_2H$, all $1\le h\le H-1$ and all $(s,a)\in\mathcal S\times\mathcal A$,
--   $$\Big|\big(\widehat P_h-P_h\big)V^{(l)}_{h+1}\Big|(s,a)\le\sqrt{\frac{\beta_1}{N}}\sqrt{\mathrm{Var}_{P_h}\big[V^{(l)}_{h+1}\big](s,a)}+\frac{\beta_1\|V^{(l)}_{h+1}\|_\infty}{N}.\tag{66}$$
--
--   This is the concentration step for the optimal policy $\pi^\star$ in the proof of Theorem 4: a fixed policy's auxiliary vectors are independent of the data, so Bernstein's inequality and a union bound apply. Holding for every action $a$, it implies the condition (63) of Lemma 9 for $\pi$.
--
--   **Formalization Note** The page takes $\pi=\pi^\star$; the statement here holds for every data-independent policy, which contains that case. "With probability at least $1-\delta$" is written as: the probability of the failure event is at most $\delta$. Steps are 0-based ($1\le h\le H-1$ is `h.val + 1 < H`). $N>0$ is the standing assumption of (6).
-- source:
--   arXiv:2005.12900v8, §7.3, first bullet, (66)–(67), p. 21

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_BreakingSample_FiniteHorizon_Model
import Definitions.Def_BreakingSample_FiniteHorizon_Sampling

namespace BreakingSample.FiniteHorizon

/-- (66)–(67), §7.3, first bullet (arXiv:2005.12900v8, p. 21), for any fixed (data-independent) policy `π`
(the page takes `π = π⋆`): with probability at least `1 − δ` over the data, for all `0 ≤ l ≤ log₂ H`, all
paper steps `1 ≤ h ≤ H − 1` (Lean: `h.val + 1 < H`) and all `(s,a)`,
`|(P̂_h − P_h)V⁽ˡ⁾_{h+1}|(s,a) ≤ √(β₁/N) √(Var_{P_h}(V⁽ˡ⁾_{h+1})(s,a)) + β₁‖V⁽ˡ⁾_{h+1}‖∞/N` with
`β₁ = 4 log(H|S||A|/δ)`. Written as a bound on the probability of the failure event. -/
theorem eq_66_67 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] {H : ℕ}
    (P : Fin H → S → A → S → ℝ) (r : Fin H → S → A → ℝ) (hM : IsFHMDP P r) (π : Fin H → S → A)
    (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (hN : 0 < N) :
    sampleProb P N (fun x => ¬ ∀ l : ℕ, (l : ℝ) ≤ Real.logb 2 H → ∀ h : Fin H, h.val + 1 < H →
      ∀ (s : S) (a : A),
        |∑ s', (empKernel x h s a s' - P h s a s') *
            propagate P π (auxReward P r π l) (h.val + 1) s'| ≤
          Real.sqrt (4 * Real.log ((H : ℝ) * Fintype.card S * Fintype.card A / δ) / N) *
              Real.sqrt (varSA P h (propagate P π (auxReward P r π l) (h.val + 1)) s a) +
            4 * Real.log ((H : ℝ) * Fintype.card S * Fintype.card A / δ) *
              ‖propagate P π (auxReward P r π l) (h.val + 1)‖ / N) ≤ δ := by sorry

end BreakingSample.FiniteHorizon
