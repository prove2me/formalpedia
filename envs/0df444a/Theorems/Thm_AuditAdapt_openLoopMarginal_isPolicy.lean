-- Prove2me | Theorems.Thm_AuditAdapt_openLoopMarginal_isPolicy
-- name    : AuditAdapt.openLoopMarginal_isPolicy
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:03:46.23751+00:00
-- url     : https://prove2.me/theorems/64843a9b-dd13-4e6f-8bf9-4fd395866370
-- title:
--   Definition 2.1, p.3 — the open-loop marginal $\nu^\pi$ is a Markov policy
-- statement:
--   Let $\pi$ be a Markov policy in a finite-horizon MDP, and let $\nu^\pi$ be its open-loop marginal, $\nu^\pi_t(\cdot\mid s)=\bar p^\pi_t$ for all $s$, where $\bar p^\pi_t(a)=\sum_s d^\pi_t(s)\pi_t(a\mid s)$. Then $\nu^\pi$ is a Markov policy: for every $t=1,\dots,H$,
--
--   $$
--   \bar p^\pi_t(a)\ge0\quad\text{for all }a\in\mathcal A,\qquad\sum_{a\in\mathcal A}\bar p^\pi_t(a)=1 .
--   $$
--
--   Definition 2.1 calls $\nu^\pi$ "the policy"; this theorem records that it is one, so that $J(\nu^\pi)$, $Q^{\nu}_t$ and $V^{\nu}_t$ are the quantities of a Markov policy.
--
--   Differences from the source:
--   - encoding: steps t = 1, …, H and the terminal convention V^μ_{H+1} ≡ 0 → 0-based layers t ∈ Finset.range H, terminal V M μ H = 0; reason: index shift only (layer t is the paper's step t + 1)
--   - encoding: Markov policy π = (π_t)_{t≤H} with π_t(· | s) ∈ Δ(A) → π : ℕ → S → A → ℝ with IsPolicy H π (a distribution at every layer < H and every state); reason: values at layers ≥ H are never used; same instances
--   - encoding: kernels P_t(· | s, a) ∈ Δ(S) for t ≤ H → EpisodicMDP field P h, a distribution for every h ∈ ℕ (P_sum_one); reason: kernels beyond the horizon are never used; every paper MDP extends (repeat P_H)
-- source:
--   Aldridge, Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing Adaptive Policies, STOC 2027 submission (held version, sha256 3f6ad545b0454d8de6836d32bb81359da5022bbc373510a7c75452ab66ec9fc2), Definition 2.1 (Open-loop marginal), p.3

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_AuditAdapt_stateLaw
import Definitions.Def_AuditAdapt_openLoopMarginal

namespace AuditAdapt

open FoundationsRL.RLBasics

/-- **Definition 2.1, p.3: `ν^π` is a Markov policy** (Aldridge, *Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing
Adaptive Policies*, STOC 2027 submission (held version, sha256 3f6ad545…)). If `π` is a Markov
policy then its open-loop marginal `ν^π`, `ν^π_t(· | s) = p̄^π_t`, is a Markov policy: `p̄^π_t ∈ Δ(A)`
for every `t = 1, …, H`.

**Formalization Note** 0-based layers; `IsPolicy H` constrains exactly the layers `t < H`. -/
theorem openLoopMarginal_isPolicy {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π) :
    IsPolicy H (openLoopMarginal M π) := by sorry

end AuditAdapt
