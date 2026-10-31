-- Prove2me | Theorems.Thm_FairExplore_proposition_3
-- name    : FairExplore.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:16:33.671982+00:00
-- url     : https://prove2.me/theorems/1558d9b0-3b32-4df5-97b7-0e0c0258ee40
-- title:
--   Proposition 3, p.16 — the minimum-norm solution of $P(\hat\theta)$ is close to $q^*$ when $\hat\theta$ is close to $\theta$
-- statement:
--   Let $\theta\in(0,1)^K$ have distinct entries, let every group have an arm and every arm a group, and let $q_*$ be the optimal solution of (13) with the smallest Euclidean norm. For any $\varepsilon>0$ there exists $\delta>0$ such that for every vector $\tilde\theta$ with $\tilde\theta(a)\in[\theta(a)-\delta,\theta(a)+\delta]$ for all arms $a$, the minimum-norm optimal solution $\hat q$ of $P(\tilde\theta)$ satisfies
--   $$\hat q^g(a)\in[q^g_*(a)-\varepsilon,\ q^g_*(a)+\varepsilon]\qquad\text{for all }a\in\mathcal A,\ g\in G.$$
--   In particular, on the event $H_t(\delta)$ PF-UCB's $\hat q_t$ is within $\varepsilon$ of $q_*$.
--
--   Neither program is assumed to have a unique optimum: the statement is about the minimum-norm selections.
--
--   Differences from the source:
--   - reading: "if H_t(δ), then q̂^g_t(a) ∈ [q^g_*(a) − ε, q^g_*(a) + ε]" → for every real vector θ̃ within δ of θ, qhat θ̃ is within ε of qhat θ; reason: a deterministic statement about the program; on H_t(δ) the estimate θ̂_t is such a vector on every sample path, so it implies the printed form
--   - encoding: A^g unrestricted → every A^g nonempty; reason: OPT(g) = max over A^g and the pull A_t ∈ A^{g_t} are undefined otherwise
--   - encoding: G_a unrestricted → every arm belongs to some group; reason: J(a) = max over G_a is undefined otherwise and (13) is infeasible (Σ_g q^g(a) = 1 with every q^g(a) = 0)
-- source:
--   Baek & Farias, Fair Exploration via Axiomatic Bargaining, arXiv:2106.02553v2, Proposition 3, p.16 (proof pp.47–50)

import Mathlib
import Definitions.Def_FairExplore_Program

namespace FairExplore

/-- Proposition 3 (stability of the minimum-norm solution): for any `ε > 0` there is `δ > 0` such
that if `H_t(δ)`, i.e. `θ̂_t(a) ∈ [θ(a) − δ, θ(a) + δ]` for all `a`, then
`q̂^g_t(a) ∈ [q^g_*(a) − ε, q^g_*(a) + ε]` for all `a ∈ A` and `g ∈ G`.
Baek & Farias, *Fair Exploration via Axiomatic Bargaining*, arXiv:2106.02553v2, Proposition 3, p.16 (proof pp.47–50).

**Formalization Note** Stated deterministically for every vector `θ̃` within `δ` of `θ` (the
estimate `θ̂_t` is such a vector on `H_t(δ)`, on every sample path), with `q̂ = qhat A θ̃` and
`q_* = qhat A θ`, the minimum-norm optimal solutions (no uniqueness of the optimum is assumed). -/
theorem proposition_3 {γ α : Type*} [Fintype γ] [Fintype α] [DecidableEq α]
    (A : γ → Finset α) (hA : ∀ g, (A g).Nonempty) (hG : ∀ a, ∃ g, a ∈ A g)
    (θ : α → ℝ) (hθ : InKClass θ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ θ' : α → ℝ,
      (∀ a, θ' a ∈ Set.Icc (θ a - δ) (θ a + δ)) →
        ∀ g a, qhat A θ' g a ∈ Set.Icc (qhat A θ g a - ε) (qhat A θ g a + ε) := by sorry

end FairExplore
