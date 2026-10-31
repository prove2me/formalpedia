-- Prove2me | Theorems.Thm_FairExplore_min_norm_solution_exists_unique
-- name    : FairExplore.min_norm_solution_exists_unique
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:16:48.212031+00:00
-- url     : https://prove2.me/theorems/6427aa28-4cf0-47f6-97be-4e548e043db2
-- title:
--   §4.1, p.14 — program $P(\tilde\theta)$ has a unique optimal solution of minimum Euclidean norm
-- statement:
--   Let $\tilde\theta$ be any real vector of arm parameters (the true $\theta$, or an estimate $\hat\theta_t$), and suppose every arm belongs to some group. Then program (13) at $\tilde\theta$,
--   $$\max_{q\ge0}\ \sum_{g}\log\Big(\sum_{a\in\tilde{\mathcal A}^g_{\mathrm{sub}}}\tilde\Delta^g(a)\big(\tilde J^g(a)-q^g(a)\tilde J(a)\big)\Big)\quad\text{s.t.}\quad \sum_g q^g(a)=1\ (a\in\tilde{\mathcal A}_{\mathrm{sub}}),\ \ q^g(a)=0\ (a\notin\tilde{\mathcal A}_{\mathrm{sub}}\cap\mathcal A^g),$$
--   has exactly one optimal solution whose Euclidean norm $\sum_{g,a}q^g(a)^2$ is smallest among all optimal solutions.
--
--   This is what makes PF-UCB's $\hat q_t$ ("the solution … with the smallest Euclidean norm", p.14) and the target $q^*$ of (14) well defined, without assuming that (13) has a unique optimum.
--
--   **Formalization Note** The objective takes values in the extended reals with $\log u=-\infty$ for $u\le0$; when every feasible point has value $-\infty$, every feasible point is optimal.
--
--   Differences from the source:
--   - reading: "define q̂ to be the solution … with the smallest Euclidean norm" (presupposed, not stated) → ∃! q, IsMinNormOpt A θ̃ q, for every real vector θ̃; reason: the paper uses the object for θ̂_t and θ; the claim it presupposes is stated as a theorem so that the defined qhat is the paper's
--   - encoding: G_a unrestricted → every arm belongs to some group; reason: J(a) = max over G_a is undefined otherwise and (13) is infeasible (Σ_g q^g(a) = 1 with every q^g(a) = 0)
-- source:
--   Baek & Farias, Fair Exploration via Axiomatic Bargaining, arXiv:2106.02553v2, §4.1, p.14 (unnumbered: "the solution to the following optimization problem with the smallest Euclidean norm"); (14), p.15

import Mathlib
import Definitions.Def_FairExplore_Program

namespace FairExplore

/-- For every parameter vector `θ̃` (the true `θ` or an estimate `θ̂_t`), the program (13)
(equivalently `P(θ̃)`) has exactly one optimal solution of smallest Euclidean norm.
Baek & Farias, *Fair Exploration via Axiomatic Bargaining*, arXiv:2106.02553v2, §4.1, p.14 (unnumbered): "define (q̂^g_t(a))_{g∈G,a∈A^g} to be the solution to the following
optimization problem with the smallest Euclidean norm"; p.15: "q* is the optimal solution to (13)
with the smallest Euclidean norm".

**Formalization Note** `θ̃` is any real vector (estimates may leave `(0,1)` and may tie). Every arm
belongs to some group (otherwise `J(a)` is undefined and (13) is infeasible). The norm is
`∑_{g,a} q^g(a)²`; entries off `A^g` are `0` in every feasible point. -/
theorem min_norm_solution_exists_unique {γ α : Type*} [Fintype γ] [Fintype α] [DecidableEq α]
    (A : γ → Finset α) (hG : ∀ a, ∃ g, a ∈ A g) (θ : α → ℝ) :
    ∃! q : γ → α → ℝ, IsMinNormOpt A θ q := by sorry

end FairExplore
