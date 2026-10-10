-- Prove2me | Theorems.Thm_BayesProphet_MultiSec_offline_satisfaction
-- name    : BayesProphet.MultiSec.offline_satisfaction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:46:45.980671+00:00
-- url     : https://prove2.me/theorems/fcdd151d-43d6-4c3b-b884-5c697aadb3fb
-- title:
--   App. B.3 conditions (1)–(2) — when Offline is not satisfied rejecting or accepting
-- statement:
--   In the multi-secretary problem with non-negative rewards $r_j\ge0$, fix a sample path, a time-to-go $t\ge1$ and a budget $b\ge1$, and let $j=\theta^t$ be the current arrival. Then:
--
--   1. Offline is not satisfied rejecting the current arrival iff every optimal offline solution (sort the arrivals $\theta^t,\dots,\theta^1$ by reward and keep the top $b$) takes all arrivals of its reward level, i.e.
--   $$r_j>0\quad\text{and}\quad \#\{\tau\in\{1,\dots,t-1\}:\ r_{\theta^\tau}\ge r_j\}<b;$$
--   2. Offline is not satisfied accepting the current arrival iff every optimal offline solution rejects it, i.e.
--   $$\#\{\tau\in\{1,\dots,t-1\}:\ r_{\theta^\tau}>r_j\}\ge b.$$
--
--   These are the paper's conditions "(1) Offline is not satisfied rejecting a class $j$ iff he accepts all the future arrivals type $j$" and "(2) Offline is not satisfied accepting class $j$ iff he rejects all future type $j$ arrivals", which reduce the disagreement events of the Fluid Bayes Selector to binomial tail events.
--
--   **Formalization Note** "Not satisfied" is the disagreement predicate of Definition 4 for Offline's Bellman value (2). The paper phrases the conditions through a solution $X^{\star t}$ of the ex-post problem $(P^\star_t)$; with tied rewards that solution is not unique, so the conditions are stated through the counts of strictly better and at-least-as-good arrivals among the future arrivals $\theta^{t-1},\dots,\theta^1$.
-- source:
--   Vera & Banerjee, The Bayesian Prophet: A Low-Regret Framework for Online Decision Making, SSRN 3158062 (doi:10.2139/ssrn.3158062), p. 37, Appendix B.3, conditions (1)–(2) (see also p. 17, after Algorithm 2)

import Mathlib
import Definitions.Def_BayesProphet_MultiSec_OnlineProblem
import Definitions.Def_BayesProphet_MultiSec_MultiSecretary

namespace BayesProphet.MultiSec

theorem offline_satisfaction {n : ℕ} (r : Fin n → ℝ) (hr₀ : ∀ j, 0 ≤ r j)
    (θ : ℕ → Fin n) (t b : ℕ) (ht : 1 ≤ t) (hb : 1 ≤ b) :
    ((secretaryProblem r).Disagree θ t Action.reject b ↔
        0 < r (θ t) ∧ ((Finset.Ico 1 t).filter (fun τ => r (θ t) ≤ r (θ τ))).card < b) ∧
    ((secretaryProblem r).Disagree θ t Action.accept b ↔
        b ≤ ((Finset.Ico 1 t).filter (fun τ => r (θ t) < r (θ τ))).card) := by sorry

end BayesProphet.MultiSec
