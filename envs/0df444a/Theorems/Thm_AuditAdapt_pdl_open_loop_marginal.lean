-- Prove2me | Theorems.Thm_AuditAdapt_pdl_open_loop_marginal
-- name    : AuditAdapt.pdl_open_loop_marginal
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:03:46.711074+00:00
-- url     : https://prove2.me/theorems/8da7fc0e-7854-4d67-a968-af7d2cd43a36
-- title:
--   Proof of Theorem 3.4, p.3 — Lemma 3.3 with $\mu=\nu$: $J(\pi)-J(\nu)=\sum_t\mathbb E\langle q_t,z_t-\bar p_t\rangle$
-- statement:
--   Let $\pi$ be a Markov policy in a finite-horizon MDP and $\nu=\nu^\pi$ its open-loop marginal, with average action distributions $\bar p_t$. Write $q_t=Q^\nu_t(s_t,\cdot)$ and $z_t=\pi_t(\cdot\mid s_t)$ with $s_t\sim d^\pi_t$. Then
--
--   $$
--   J(\pi)-J(\nu)=\sum_{t=1}^H\mathbb E_{s_t\sim d^\pi_t}\langle q_t,z_t-\bar p_t\rangle=\sum_{t=1}^H\sum_{s}d^\pi_t(s)\sum_a Q^\nu_t(s,a)\big(\pi_t(a\mid s)-\bar p_t(a)\big).
--   $$
--
--   This is the first display of the proof of Theorem 3.4. It is Lemma 3.3 with $\mu=\nu$, combined with $V^\nu_t(s)=\langle Q^\nu_t(s,\cdot),\bar p_t\rangle$, which holds because $\nu_t(\cdot\mid s)=\bar p_t$ for every $s$.
--
--   Differences from the source:
--   - encoding: steps t = 1, …, H and the terminal convention V^μ_{H+1} ≡ 0 → 0-based layers t ∈ Finset.range H, terminal V M μ H = 0; reason: index shift only (layer t is the paper's step t + 1)
--   - encoding: Markov policy π = (π_t)_{t≤H} with π_t(· | s) ∈ Δ(A) → π : ℕ → S → A → ℝ with IsPolicy H π (a distribution at every layer < H and every state); reason: values at layers ≥ H are never used; same instances
--   - encoding: kernels P_t(· | s, a) ∈ Δ(S) for t ≤ H → EpisodicMDP field P h, a distribution for every h ∈ ℕ (P_sum_one); reason: kernels beyond the horizon are never used; every paper MDP extends (repeat P_H)
--   - encoding: bounded costs ℓ_t : S × A → ℝ → EpisodicMDP field R t, an arbitrary real function (documented on the platform as a mean reward); reason: S and A are finite, so every real function is bounded; R is used as the cost with no sign change
--   - encoding: J(π) = E^π[Σ_t ℓ_t(s_t, a_t)] → totalCost M π = Σ_t Σ_s d^π_t(s) Σ_a π_t(a | s) ℓ_t(s, a); reason: linearity of expectation over the law P_t(s,a) = d^π_t(s) π_t(a | s) of (s_t, a_t); same value
-- source:
--   Aldridge, Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing Adaptive Policies, STOC 2027 submission (held version, sha256 3f6ad545b0454d8de6836d32bb81359da5022bbc373510a7c75452ab66ec9fc2), proof of Theorem 3.4, p.3

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_AuditAdapt_stateLaw
import Definitions.Def_AuditAdapt_totalCost
import Definitions.Def_AuditAdapt_openLoopMarginal

namespace AuditAdapt

open FoundationsRL.RLBasics

/-- **Proof of Theorem 3.4, p.3: Lemma 3.3 with `μ = ν`** (Aldridge, *Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing
Adaptive Policies*, STOC 2027 submission (held version, sha256 3f6ad545…)). For a Markov policy
`π` and its open-loop marginal `ν = ν^π`, `J(π) − J(ν) = ∑_t E_{s_t∼d^π_t}⟨q_t, z_t − p̄_t⟩`, where
`q_t = Q^ν_t(s_t, ·)` and `z_t = π_t(· | s_t)`.

**Formalization Note** 0-based layers; `p̄_t` is `marginal M π t`, `d^π_t` is `stateLaw M π t`. -/
theorem pdl_open_loop_marginal {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π) :
    totalCost M π - totalCost M (openLoopMarginal M π) =
      ∑ t ∈ Finset.range H, ∑ s : S, stateLaw M π t s *
        ∑ a : A, Q M (openLoopMarginal M π) t s a * (π t s a - marginal M π t a) := by sorry

end AuditAdapt
