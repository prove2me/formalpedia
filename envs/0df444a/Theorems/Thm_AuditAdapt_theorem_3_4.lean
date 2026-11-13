-- Prove2me | Theorems.Thm_AuditAdapt_theorem_3_4
-- name    : AuditAdapt.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:06:23.438355+00:00
-- url     : https://prove2.me/theorems/005ff413-17ec-4909-a18d-ffbb12f558f4
-- title:
--   Theorem 3.4, p.3 — covariance characterization: $J(\pi)-J(\nu^\pi)=\sum_t\operatorname{tr}\operatorname{Cov}(Q^\nu_t(s_t,\cdot),\pi_t(\cdot\mid s_t))$
-- statement:
--   Let $M=(\mathcal S,\mathcal A,H,(P_t)_{t\le H},(\ell_t)_{t\le H},\rho)$ be a finite-horizon MDP with finite state and action sets, and let $\pi$ be a (randomized, time-dependent) Markov policy. Let $\nu=\nu^\pi$ be its open-loop marginal, $\nu_t(\cdot\mid s)=\bar p_t$ with $\bar p_t(a)=\sum_s d^\pi_t(s)\pi_t(a\mid s)$, and write $q_t=Q^\nu_t(s_t,\cdot)$, $z_t=\pi_t(\cdot\mid s_t)$ with $s_t\sim d^\pi_t$. Let $P_t(s,a)=d^\pi_t(s)\pi_t(a\mid s)$ be the joint law of $(s_t,a_t)$, with marginals $P^S_t=d^\pi_t$ and $P^A_t=\bar p_t$. Then
--
--   $$
--   J(\pi)-J(\nu)=\sum_{t=1}^H\operatorname{tr}\operatorname{Cov}(q_t,z_t)\tag{3}
--   $$
--
--   $$
--   \qquad\quad=\sum_{t=1}^H\Big(\mathbb E_{(s,a)\sim P_t}\big[Q^\nu_t(s,a)\big]-\mathbb E_{(s,a)\sim P^S_t\otimes P^A_t}\big[Q^\nu_t(s,a)\big]\Big).\tag{4}
--   $$
--
--   Moreover, each summand of (3) and of (4) is unchanged if $Q^\nu_t(s,a)$ is replaced by $Q^\nu_t(s,a)-g_t(s)$, for any $g_t:\mathcal S\to\mathbb R$.
--
--   The identity holds under fully endogenous dynamics: actions influence future states, and this feedback is accounted for by averaging over the policy's own state laws $d^\pi_t$ and by scoring actions with the action-values of $\nu$, not of $\pi$ and not the immediate costs. The adaptivity cost $J(\pi)-J(\nu^\pi)$ is therefore a sum of covariances between the action-values of the open-loop marginal and the policy's state-dependent action distribution; the invariance allows $Q^\nu_t$ to be replaced by the advantage $Q^\nu_t-V^\nu_t$.
--
--   **Formalization Note** The MDP, policies, $Q$ and $V$ are those of the published `FoundationsRL.RLBasics` layer, with $\rho$ = `d1` and $\ell_t$ = `R t`. $\operatorname{tr}\operatorname{Cov}$ is the form $\mathbb E\langle q,z\rangle-\langle\mathbb Eq,\mathbb Ez\rangle$ of §2 (`trCov`), and the summands of (4) are `jointMinusProduct`. The only hypothesis on $\pi$ is that it is a Markov policy; that $\nu$ is one is a theorem of the mission, not an assumption.
--
--   Differences from the source:
--   - encoding: steps t = 1, …, H and the terminal convention V^μ_{H+1} ≡ 0 → 0-based layers t ∈ Finset.range H, terminal V M μ H = 0; reason: index shift only (layer t is the paper's step t + 1)
--   - encoding: Markov policy π = (π_t)_{t≤H} with π_t(· | s) ∈ Δ(A) → π : ℕ → S → A → ℝ with IsPolicy H π (a distribution at every layer < H and every state); reason: values at layers ≥ H are never used; same instances
--   - encoding: kernels P_t(· | s, a) ∈ Δ(S) for t ≤ H → EpisodicMDP field P h, a distribution for every h ∈ ℕ (P_sum_one); reason: kernels beyond the horizon are never used; every paper MDP extends (repeat P_H)
--   - encoding: bounded costs ℓ_t : S × A → ℝ → EpisodicMDP field R t, an arbitrary real function (documented on the platform as a mean reward); reason: S and A are finite, so every real function is bounded; R is used as the cost with no sign change
--   - encoding: J(π) = E^π[Σ_t ℓ_t(s_t, a_t)] → totalCost M π = Σ_t Σ_s d^π_t(s) Σ_a π_t(a | s) ℓ_t(s, a); reason: linearity of expectation over the law P_t(s,a) = d^π_t(s) π_t(a | s) of (s_t, a_t); same value
--   - reading: "each summand is unchanged" (the sentence does not say whether the summands of (3) or of (4) are meant) → the invariance is stated for the summands of both (3) and (4), at every step; reason: the stronger of the two readings; the proof on p.3 shows both
-- source:
--   Aldridge, Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing Adaptive Policies, STOC 2027 submission (held version, sha256 3f6ad545b0454d8de6836d32bb81359da5022bbc373510a7c75452ab66ec9fc2), Theorem 3.4 (Covariance characterization), displays (3) and (4), p.3

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_AuditAdapt_stateLaw
import Definitions.Def_AuditAdapt_totalCost
import Definitions.Def_AuditAdapt_openLoopMarginal
import Definitions.Def_AuditAdapt_trCov
import Definitions.Def_AuditAdapt_jointMinusProduct

namespace AuditAdapt

open FoundationsRL.RLBasics

/-- **Theorem 3.4 (Covariance characterization), p.3** (Aldridge, *Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing
Adaptive Policies*, STOC 2027 submission (held version, sha256 3f6ad545…)). For every finite-horizon
MDP and every Markov policy `π`, with `ν = ν^π`,
`J(π) − J(ν) = ∑_{t=1}^H tr Cov(q_t, z_t)` (3)
`= ∑_{t=1}^H (E_{(s,a)∼P_t}[Q^ν_t(s,a)] − E_{(s,a)∼P^S_t⊗P^A_t}[Q^ν_t(s,a)])` (4).
Moreover, each summand is unchanged if `Q^ν_t(s,a)` is replaced by `Q^ν_t(s,a) − g_t(s)` for any
`g_t : S → ℝ`.

**Formalization Note** 0-based layers: `t ∈ Finset.range H` is the paper's `t = 1, …, H`; the
published `V M μ H = 0` is `V^μ_{H+1} ≡ 0`. `q_t = Q^ν_t(s_t, ·)`, `z_t = π_t(· | s_t)`, `s_t ∼ d^π_t`,
where `d^π_t` is the `ρ`-mixture `stateLaw` of the published `stateDist`. The cost `ℓ_t` is the
field `M.R t` (documented as a mean reward on the platform; the identity is linear, so no sign
change). `J` is `∑_t E_{d^π_t}⟨ℓ_t, π_t⟩` (`totalCost`), and `tr Cov` is the form
`E⟨q,z⟩ − ⟨Eq,Ez⟩` (`trCov`). "Each summand" is stated for the summands of both (3) and (4). -/
theorem theorem_3_4 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π) :
    (totalCost M π - totalCost M (openLoopMarginal M π) =
        ∑ t ∈ Finset.range H, trCov M π t (Q M (openLoopMarginal M π) t)) ∧
    (totalCost M π - totalCost M (openLoopMarginal M π) =
        ∑ t ∈ Finset.range H, jointMinusProduct M π t (Q M (openLoopMarginal M π) t)) ∧
    (∀ g : ℕ → S → ℝ, ∀ t, t < H →
        trCov M π t (fun s a => Q M (openLoopMarginal M π) t s a - g t s) =
            trCov M π t (Q M (openLoopMarginal M π) t) ∧
        jointMinusProduct M π t (fun s a => Q M (openLoopMarginal M π) t s a - g t s) =
            jointMinusProduct M π t (Q M (openLoopMarginal M π) t)) := by sorry

end AuditAdapt
