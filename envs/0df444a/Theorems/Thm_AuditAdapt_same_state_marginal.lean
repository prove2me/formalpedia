-- Prove2me | Theorems.Thm_AuditAdapt_same_state_marginal
-- name    : AuditAdapt.same_state_marginal
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:03:40.046027+00:00
-- url     : https://prove2.me/theorems/404f279f-363a-4556-86a8-bf9cef67e8c4
-- title:
--   Proof of Theorem 3.4, p.3 — $P_t$ and $P^S_t\otimes P^A_t$ have the same $s$-marginal
-- statement:
--   Let $\pi$ be a Markov policy in a finite-horizon MDP, let $P_t(s,a)=d^\pi_t(s)\pi_t(a\mid s)$ be the joint law of $(s_t,a_t)$ and $P^S_t\otimes P^A_t$, $(s,a)\mapsto d^\pi_t(s)\bar p^\pi_t(a)$, the product of its marginals. For every $t=1,\dots,H$ and every function $g_t:\mathcal S\to\mathbb R$ of the state,
--
--   $$
--   \mathbb E_{(s,a)\sim P_t}[g_t(s)]=\mathbb E_{(s,a)\sim P^S_t\otimes P^A_t}[g_t(s)] .
--   $$
--
--   This is the last step of the proof of Theorem 3.4: it gives the invariance of the summands of (4) under $Q^\nu_t\mapsto Q^\nu_t-g_t$.
--
--   Differences from the source:
--   - encoding: steps t = 1, …, H and the terminal convention V^μ_{H+1} ≡ 0 → 0-based layers t ∈ Finset.range H, terminal V M μ H = 0; reason: index shift only (layer t is the paper's step t + 1)
--   - encoding: Markov policy π = (π_t)_{t≤H} with π_t(· | s) ∈ Δ(A) → π : ℕ → S → A → ℝ with IsPolicy H π (a distribution at every layer < H and every state); reason: values at layers ≥ H are never used; same instances
--   - encoding: kernels P_t(· | s, a) ∈ Δ(S) for t ≤ H → EpisodicMDP field P h, a distribution for every h ∈ ℕ (P_sum_one); reason: kernels beyond the horizon are never used; every paper MDP extends (repeat P_H)
-- source:
--   Aldridge, Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing Adaptive Policies, STOC 2027 submission (held version, sha256 3f6ad545b0454d8de6836d32bb81359da5022bbc373510a7c75452ab66ec9fc2), proof of Theorem 3.4, p.3

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_AuditAdapt_stateLaw
import Definitions.Def_AuditAdapt_openLoopMarginal

namespace AuditAdapt

open FoundationsRL.RLBasics

/-- **Proof of Theorem 3.4, p.3: `P_t` and `P^S_t ⊗ P^A_t` have the same `s`-marginal**
(Aldridge, *Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing
Adaptive Policies*, STOC 2027 submission (held version, sha256 3f6ad545…)). For a Markov policy `π`, every layer `t = 1, …, H` and every `g : S → ℝ`,
`E_{P_t} g = E_{P^S_t ⊗ P^A_t} g`, where `P_t(s,a) = d^π_t(s) π_t(a|s)` and
`(P^S_t ⊗ P^A_t)(s,a) = d^π_t(s) p̄^π_t(a)`.

**Formalization Note** 0-based layers; `g` is an arbitrary real function of the state. -/
theorem same_state_marginal {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π) (t : ℕ) (ht : t < H)
    (g : S → ℝ) :
    ∑ s : S, ∑ a : A, stateLaw M π t s * π t s a * g s =
      ∑ s : S, ∑ a : A, stateLaw M π t s * marginal M π t a * g s := by sorry

end AuditAdapt
