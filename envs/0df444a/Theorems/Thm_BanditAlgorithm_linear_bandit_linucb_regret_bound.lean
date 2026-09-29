-- Prove2me | Theorems.Thm_BanditAlgorithm_linear_bandit_linucb_regret_bound
-- name    : BanditAlgorithm.linear_bandit_linucb_regret_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-29T16:39:07.874715+00:00
-- url     : https://prove2.me/theorems/1a5b1fe7-553d-4ce4-8122-44de756f3b8e
-- statement:
--   (LinUCB/OFUL regret, GOAL — Theorem 19.2, stated pathwise) Under Assumption 19.1:
--
--   - (a) $1 \le \beta_1 \le \cdots \le \beta_n$;
--   - (b) $\max_{t\in[n]} \sup_{a,b\in\mathcal{A}_t}\langle\theta_*, a-b\rangle \le 1$;
--   - (c) $\|a\|_2 \le L$ for all $a\in\bigcup_{t=1}^n\mathcal{A}_t$ —
--
--   if the sequences form a LinUCB trace (Eqs. 19.2/19.3/19.7/19.12) and $\theta_* \in \mathcal{C}_t$ for all $t\in[n]$ (the $1-\delta$ event of Assumption 19.1(d), taken as a hypothesis; its probabilistic wrapper is Mission IX's Theorem 20.5), then
--
--   $$\hat R_n \le \sqrt{8n\beta_n\log\frac{\det V_n(\lambda)}{\det V_0(\lambda)}} \le \sqrt{8dn\beta_n\log\frac{d\lambda+nL^2}{d\lambda}}$$
--
--   — both inequalities, as in the book.
-- source:
--   L&S Theorem 19.2 with Assumption 19.1, p.243

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_StochasticLinearBandit


open Matrix

theorem BanditAlgorithm.linear_bandit_linucb_regret_bound {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    {lam L : ℝ} (hlam : 0 < lam)
    (𝓐 𝓒 : ℕ → Set (Fin d → ℝ)) (β : ℕ → ℝ)
    (a θtilde astar : ℕ → Fin d → ℝ) (x : ℕ → ℝ) (θstar : Fin d → ℝ)
    -- Assumption 19.1 (a): `1 ≤ β_1 ≤ β_2 ≤ ⋯ ≤ β_n`
    (hβ_one : 1 ≤ β 1)
    (hβ_mono : ∀ s t : ℕ, 1 ≤ s → s ≤ t → t ≤ n → β s ≤ β t)
    -- Assumption 19.1 (b): `max_{t∈[n]} sup_{a,b∈𝓐_t} ⟨θ*, a − b⟩ ≤ 1`
    (hb : ∀ t ∈ Finset.range n, ∀ b ∈ 𝓐 (t + 1), ∀ b' ∈ 𝓐 (t + 1),
      θstar ⬝ᵥ (b - b') ≤ 1)
    -- Assumption 19.1 (c): `‖a‖₂ ≤ L` for all `a ∈ ⋃_{t=1}^n 𝓐_t`
    (hL : ∀ t ∈ Finset.range n, ∀ b ∈ 𝓐 (t + 1), Real.sqrt (b ⬝ᵥ b) ≤ L)
    -- the run of LinUCB (Eqs. (19.2), (19.3), (19.7), (19.12))
    (htrace : IsLinUCBTrace lam n 𝓐 𝓒 β a θtilde astar x θstar)
    -- the `1 − δ` event of Assumption 19.1 (d): `θ* ∈ 𝓒_t` for all `t ∈ [n]`
    (hmem : ∀ t ∈ Finset.range n, θstar ∈ 𝓒 (t + 1)) :
    linearPseudoRegret θstar a astar n ≤
      Real.sqrt (8 * n * β n *
        Real.log ((regularizedDesignMatrixSeq d lam a n).det /
          (regularizedDesignMatrixSeq d lam a 0).det)) ∧
    Real.sqrt (8 * n * β n *
        Real.log ((regularizedDesignMatrixSeq d lam a n).det /
          (regularizedDesignMatrixSeq d lam a 0).det)) ≤
      Real.sqrt (8 * d * n * β n *
        Real.log ((d * lam + n * L ^ 2) / (d * lam))) := by
  sorry
