-- Prove2me | Theorems.Thm_BreakingSample_FiniteHorizon_lemma_12
-- name    : BreakingSample.FiniteHorizon.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:50.433972+00:00
-- url     : https://prove2.me/theorems/f538f2d3-dd90-44f0-adca-793d9e5ed09c
-- title:
--   Lemma 12, p. 34 — the auxiliary vectors of (62) obey ‖V^(l)_h‖∞ ≤ (√(3H))^l H
-- statement:
--   Let $(\{P_h\},\{r_h\})$ be a finite-horizon MDP on a finite state space $\mathcal S$ with horizon $H$ and rewards in $[0,1]$, and let $\pi$ be any deterministic nonstationary policy. Build the auxiliary vectors $V^{(l)}_h$ of (62): $V^{(l)}_{H+1}=0$,
--   $$r^{(0)}_h=r^\pi_h,\qquad r^{(l)}_h=\sqrt{\mathrm{Var}_{P_{h,\pi}}\big(V^{(l-1)}_{h+1}\big)}\ (l\ge1),\qquad V^{(l)}_h=r^{(l)}_h+P_{h,\pi}V^{(l)}_{h+1}.$$
--   Then for all $1\le h\le H$ and all $l\ge0$,
--   $$\big\|V^{(l)}_h\big\|_\infty\le\big(\sqrt{3H}\big)^l H.$$
--
--   The bound controls the higher-order terms that appear when Lemma 9 is applied recursively in $l$; at $l=0$ it is the range bound $V^\pi_h\le H$.
--
--   **Formalization Note** Steps are 0-based (`h : Fin H` is the paper's step $h+1$). The policy is arbitrary; only the true kernels and the rewards enter.
-- source:
--   arXiv:2005.12900v8, App. C, Lemma 12, (112), p. 34; (62), p. 20

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_BreakingSample_FiniteHorizon_Model

namespace BreakingSample.FiniteHorizon

/-- Lemma 12 (arXiv:2005.12900v8, App. C, (112), p. 34): for any policy `π` of a finite-horizon MDP with
rewards in `[0,1]`, the auxiliary vectors `V⁽ˡ⁾_h` of (62) obey `‖V⁽ˡ⁾_h‖∞ ≤ (√(3H))ˡ H` for every step
and every `l ≥ 0`. The paper's step `h ∈ [H]` is `h.val + 1`; `V⁽ˡ⁾_h` is
`propagate P π (auxReward P r π l) h.val`. -/
theorem lemma_12 {S A : Type} [Fintype S] {H : ℕ}
    (P : Fin H → S → A → S → ℝ) (r : Fin H → S → A → ℝ) (hM : IsFHMDP P r) (π : Fin H → S → A) :
    ∀ (h : Fin H) (l : ℕ),
      ‖propagate P π (auxReward P r π l) h.val‖ ≤ Real.sqrt (3 * (H : ℝ)) ^ l * H := by sorry

end BreakingSample.FiniteHorizon
