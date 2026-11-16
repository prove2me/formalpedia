-- Prove2me | Theorems.Thm_AuditAdapt_Supplement_theorem_4_2
-- name    : AuditAdapt.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T19:37:16.441673+00:00
-- url     : https://prove2.me/theorems/674a4be8-b770-465c-afb3-39cfcf5257ee
-- title:
--   Theorem 4.2, p.4 — information bound: $|J(\pi)-J(\nu^\pi)|\le\sum_t\mathrm{span}_t(\pi)\sqrt{I(s_t;a_t)/2}$
-- statement:
--   Let $M$ be a finite-horizon MDP with finite state and action sets and arbitrary real costs, let $\pi$ be a (randomized, time-dependent) Markov policy, and let $\nu^\pi$ be its open-loop marginal. Then
--
--   $$
--   \big|J(\pi)-J(\nu^\pi)\big|\ \le\ \sum_{t=1}^H\mathrm{span}_t(\pi)\sqrt{\frac{I(s_t;a_t)}{2}},
--   $$
--
--   where $\mathrm{span}_t(\pi)$ is the action span (Definition 4.1) and $I(s_t;a_t)$ is the mutual information, in nats, between state and action at step $t$ under $\pi$.
--
--   The adaptivity cost of a policy is controlled by how much information its actions carry about the state: a policy whose actions are nearly independent of the state behaves nearly like its open-loop marginal. The constant $1/\sqrt2$ is sharp (Proposition 4.3).
--
--   **Formalization Note** $J$, $\nu^\pi$, $d^\pi_t$, $\bar p_t$ and $Q$ are the published objects of the base mission and of `FoundationsRL.RLBasics`; no bounded-cost hypothesis is added.
--
--   Differences from the source:
--   - encoding: steps t = 1, …, H → 0-based layers t ∈ Finset.range H (layer t is the paper's step t + 1); reason: index shift only
--   - encoding: Markov policy π = (π_t)_{t≤H} with π_t(· | s) ∈ Δ(A) → π : ℕ → S → A → ℝ with IsPolicy H π (a distribution at every layer < H and every state); reason: values at layers ≥ H are never used; same instances
--   - encoding: kernels P_t(· | s, a) ∈ Δ(S) for t ≤ H → EpisodicMDP field P h, a distribution for every h ∈ ℕ (P_sum_one); reason: kernels beyond the horizon are never used; every paper MDP extends (repeat P_H)
--   - encoding: costs ℓ_t : S × A → ℝ → EpisodicMDP field R t (documented on the platform as a mean reward), used as the cost with no sign change; reason: same instances; S, A finite so every real function is bounded
--   - encoding: J(π) = E^π[Σ_t ℓ_t(s_t, a_t)] → the published totalCost M π = Σ_t Σ_s d^π_t(s) Σ_a π_t(a | s) ℓ_t(s, a); reason: linearity of expectation; same value
--   - encoding: span_t(π) with max/min over supp d^π_t and supp p̄_t → span M π t, ⨆/⨅ over the finite subtypes {s | 0 < d^π_t(s)} and {a | 0 < p̄_t(a)}; reason: the supports are nonempty for a Markov policy and t < H, so ⨆/⨅ are the maxima/minima
--   - encoding: I(s_t; a_t) = KL(P_t ∥ P^S_t ⊗ P^A_t) in nats → mutualInfo M π t, the published GuhaBroadcast.mutualInfo of P_t = Σ_{s,a} P_t(s,a) ln(P_t(s,a)/(P^S_t(s) P^A_t(a))) with Real.log and 0 ln 0 = 0; reason: finite-alphabet KL; the marginals of P_t are d^π_t and p̄_t for t < H; P_t ≪ P^S_t ⊗ P^A_t always, so no ∞ case
--   - encoding: finite state and action sets → S A : Type with Fintype; reason: the universe of the published GuhaBroadcast.mutualInfo; every finite set has a copy in Type
-- source:
--   Aldridge, Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing Adaptive Policies, STOC 2027 submission (held version, sha256 3f6ad545b0454d8de6836d32bb81359da5022bbc373510a7c75452ab66ec9fc2), Theorem 4.2 (Information bound), p.4 (PDF p.4)

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_AuditAdapt_stateLaw
import Definitions.Def_AuditAdapt_totalCost
import Definitions.Def_AuditAdapt_openLoopMarginal
import Definitions.Def_AuditAdapt_Supplement_span
import Definitions.Def_AuditAdapt_Supplement_mutualInfo

namespace AuditAdapt.Supplement

open FoundationsRL.RLBasics AuditAdapt

/-- **Theorem 4.2 (Information bound), p.4** (Aldridge, *Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing
Adaptive Policies*, STOC 2027 submission (held version, sha256 3f6ad545…)). For every finite-horizon MDP and every
Markov policy `π`,
`|J(π) − J(ν^π)| ≤ Σ_{t=1}^H span_t(π) √(I(s_t; a_t)/2)`,
where `I(s_t; a_t)` is the mutual information, in nats, between state and action at step `t` under `π`.

**Formalization Note** 0-based layers: `t ∈ Finset.range H` is the paper's `t = 1, …, H`. `J` is the
published `totalCost`, `ν^π` the published `openLoopMarginal`, `span_t(π)` is `span` (Definition 4.1,
`Q` of `ν^π`, maxima over `supp d^π_t` and `supp p̄_t`) and `I(s_t; a_t)` is `mutualInfo` (natural
log). The cost `ℓ_t` is `M.R t`, an arbitrary real function (no boundedness hypothesis). The only
hypothesis on `π` is that it is a Markov policy. `S`, `A` live in `Type` (the universe of the published
mutual information `GuhaBroadcast.mutualInfo`). -/
theorem theorem_4_2 {S A : Type} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π) :
    |totalCost M π - totalCost M (openLoopMarginal M π)| ≤
      ∑ t ∈ Finset.range H, span M π t * Real.sqrt (mutualInfo M π t / 2) := by sorry

end AuditAdapt.Supplement
