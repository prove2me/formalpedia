-- Prove2me | Theorems.Thm_CoffmanMitrani1980_Region_dominated_requirement_faithful
-- name    : CoffmanMitrani1980.Region.dominated_requirement_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T00:27:23.087621+00:00
-- url     : https://prove2.me/theorems/95fc100d-3bba-4184-ba45-085dddb943dc
-- title:
--   Remark after Theorem 2 (analytic form): requirements satisfying (4) with slack in (1) dominate a point of H
-- statement:
--   Consider a single server with $M\ge1$ job classes; class $i$ has arrival rate $\lambda_i>0$ and service rate $\mu_i>0$. Write $\rho_i=\lambda_i/\mu_i$, assume $\rho=\sum_i\rho_i<1$, and set $V=\sum_i\lambda_i/\mu_i^2$ and, for $g\subseteq\{1,\dots,M\}$,
--   $$f(g)=\frac{\sum_{i\in g}\rho_i/\mu_i}{1-\sum_{i\in g}\rho_i}.$$
--   Let $H$ be the set of convex combinations $\sum_{k=1}^M\alpha_kP_k$ of $M$ preemptive priority vectors. If $W\in\mathbb R^M$ satisfies
--   $$\sum_{i\in g}\rho_iW_i\ge f(g)\quad(\emptyset\ne g\subsetneq\{1,\dots,M\}),\qquad \sum_{i=1}^M\rho_iW_i>\frac{V}{1-\rho},$$
--   then there is $W'\in H$ with $W'_i\le W_i$ for every class $i$.
--
--   This is the analytic form of the remark following the proof of Theorem 2 in Coffman and Mitrani (1980): a response-time requirement that meets the inequalities (4) but exceeds the conservation law (1) is dominated by an achievable vector. Here "achievable" is replaced by membership in $H$, which Theorem 2 identifies with the achievable set; the mission's goal theorem $H^{**}=H$ is the case of equality in (1).
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28(3) (1980) 810-821, doi:10.1287/opre.28.3.810, pp. 818-819, remark following the proof of Theorem 2 (see also p. 815)

import Mathlib
import Definitions.Def_CoffmanMitrani1980_Region_Model

open Finset

theorem CoffmanMitrani1980.Region.dominated_requirement_faithful {M : ℕ} (hM : 0 < M) (p : Params M)
    (W : Fin M → ℝ)
    (hineq : ∀ g : Finset (Fin M), g.Nonempty → g ≠ univ → p.f g ≤ ∑ i ∈ g, p.rho i * W i)
    (hcons : p.V / (1 - ∑ i, p.rho i) < ∑ i, p.rho i * W i) :
    ∃ W' ∈ p.H, ∀ i, W' i ≤ W i := by sorry
