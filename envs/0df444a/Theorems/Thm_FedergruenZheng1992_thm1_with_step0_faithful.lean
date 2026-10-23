-- Prove2me | Theorems.Thm_FedergruenZheng1992_thm1_with_step0_faithful
-- name    : FedergruenZheng1992.thm1_with_step0_faithful
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-23T00:56:41.14958+00:00
-- url     : https://prove2.me/theorems/82abd06d-86cc-46a5-9050-fca1aacf7253
-- title:
--   Theorem 1 with Step 0 as printed (linear scan from $0$, $y_1>0$)
-- statement:
--   Let $K>0$ and let $G:\mathbb Z\to\mathbb R$ be such that $-G$ is unimodal (plateaus allowed) and $\lim_{|y|\to\infty}G(y)=\infty$. Let
--
--   $$C(r,Q)=\Big[K+\sum_{y=r+1}^{r+Q}G(y)\Big]\Big/Q,\qquad Q\ge1,$$
--
--   be the long-run average cost (1) of the $(r,Q)$ policy, and assume that $G$ has a global minimizer $y_1>0$. Let $L_0\ge0$ be the point where Step 0 of Algorithm OPT stops, i.e. $\Delta G(j)=G(j+1)-G(j)<0$ for $0\le j<L_0$ and $\Delta G(L_0)\ge0$. Then Step 1 of Algorithm OPT, started from $S=K+G(L_0)$, $Q=1$, $C^*=S$, $r=L_0-1$, $R=L_0+1$, stops after finitely many passes, and its output $(r,Q)$ satisfies $Q\ge1$ and
--
--   $$C(r,Q)\le C(r',Q')\qquad\text{for all } r'\in\mathbb Z,\ Q'\ge1 .$$
--
--   This is the first sentence of Theorem 1 of Federgruen and Zheng (1992), for Algorithm OPT as printed (Step 0 followed by Step 1, under the paper's convention $y_1>0$). The existing theorem FedergruenZhengRQ.OPT.algorithmOPT_optimal instead starts Step 1 from a given global minimizer, and the two agree whenever Step 0 stops at a minimizer.
--
--   **Formalization Note.** The run of Step 0 is encoded by its stopping point $L_0$ (the hypotheses determine $L_0$ uniquely). Step 1 is the platform's `optRun` with fuel $n$. Optimality is over $Q'\ge1$ because $C(r,0)$ is undefined in the paper.
-- source:
--   Federgruen and Zheng, An Efficient Algorithm for Computing an Optimal (r, Q) Policy in Continuous Review Stochastic Inventory Systems, Oper. Res. 40(4) (1992) 808-813, doi:10.1287/opre.40.4.808, p. 812, Theorem 1 (first sentence); Algorithm OPT, p. 811; model (1), p. 808

import Mathlib
import Definitions.Def_FedergruenZhengRQ_OPT_Model

open FedergruenZhengRQ.OPT

theorem FedergruenZheng1992.thm1_with_step0_faithful (κ : ℝ) (hκ : 0 < κ) (G : ℤ → ℝ)
    (hG : NegUnimodal G) (hco : Coercive G)
    (hpos : ∃ y₁ : ℤ, 0 < y₁ ∧ ∀ t, G y₁ ≤ G t)
    (L₀ : ℤ) (hL₀ : 0 ≤ L₀) (hscan : ∀ j : ℤ, 0 ≤ j → j < L₀ → G (j + 1) < G j)
    (hstop : G L₀ ≤ G (L₀ + 1)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ r : ℤ, ∃ Q : ℕ, optRun κ G L₀ n = some (r, Q) ∧ 1 ≤ Q ∧
      ∀ r' : ℤ, ∀ Q' : ℕ, 1 ≤ Q' → cost κ G r Q ≤ cost κ G r' Q' := by sorry
