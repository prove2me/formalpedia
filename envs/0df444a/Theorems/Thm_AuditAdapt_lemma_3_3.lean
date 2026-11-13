-- Prove2me | Theorems.Thm_AuditAdapt_lemma_3_3
-- name    : AuditAdapt.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:04:01.873206+00:00
-- url     : https://prove2.me/theorems/3b4c591a-211c-43fe-8a05-a780dda76524
-- title:
--   Lemma 3.3, p.3 — performance difference
-- statement:
--   Let $\pi$ and $\mu$ be Markov policies in a finite-horizon MDP. Then
--
--   $$
--   J(\pi)-J(\mu)=\sum_{t=1}^H\mathbb E_{s\sim d^\pi_t}\Big[\langle Q^\mu_t(s,\cdot),\pi_t(\cdot\mid s)\rangle-V^\mu_t(s)\Big],
--   $$
--
--   where $d^\pi_t$ is the law of $s_t$ under $\pi$ (started from $s_1\sim\rho$) and $Q^\mu_t$, $V^\mu_t$ are the action-value and value functions of $\mu$.
--
--   This is the performance difference lemma (Kakade and Langford), in the form the paper uses: the expectation is over the state laws of $\pi$, and the actions of $\pi$ are scored by the action-values of $\mu$. Theorem 3.4 applies it with $\mu=\nu^\pi$.
--
--   Differences from the source:
--   - encoding: steps t = 1, …, H and the terminal convention V^μ_{H+1} ≡ 0 → 0-based layers t ∈ Finset.range H, terminal V M μ H = 0; reason: index shift only (layer t is the paper's step t + 1)
--   - encoding: Markov policy π = (π_t)_{t≤H} with π_t(· | s) ∈ Δ(A) → π : ℕ → S → A → ℝ with IsPolicy H π (a distribution at every layer < H and every state); reason: values at layers ≥ H are never used; same instances
--   - encoding: kernels P_t(· | s, a) ∈ Δ(S) for t ≤ H → EpisodicMDP field P h, a distribution for every h ∈ ℕ (P_sum_one); reason: kernels beyond the horizon are never used; every paper MDP extends (repeat P_H)
--   - encoding: bounded costs ℓ_t : S × A → ℝ → EpisodicMDP field R t, an arbitrary real function (documented on the platform as a mean reward); reason: S and A are finite, so every real function is bounded; R is used as the cost with no sign change
--   - encoding: J(π) = E^π[Σ_t ℓ_t(s_t, a_t)] → totalCost M π = Σ_t Σ_s d^π_t(s) Σ_a π_t(a | s) ℓ_t(s, a); reason: linearity of expectation over the law P_t(s,a) = d^π_t(s) π_t(a | s) of (s_t, a_t); same value
-- source:
--   Aldridge, Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing Adaptive Policies, STOC 2027 submission (held version, sha256 3f6ad545b0454d8de6836d32bb81359da5022bbc373510a7c75452ab66ec9fc2), Lemma 3.3 (Performance difference [16]), p.3

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_AuditAdapt_stateLaw
import Definitions.Def_AuditAdapt_totalCost

namespace AuditAdapt

open FoundationsRL.RLBasics

/-- **Lemma 3.3 (Performance difference [16]), p.3** (Aldridge, *Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing
Adaptive Policies*, STOC 2027 submission (held version, sha256 3f6ad545…)). For Markov policies `π, μ`,
`J(π) − J(μ) = ∑_{t=1}^H E_{s∼d^π_t}[⟨Q^μ_t(s,·), π_t(·|s)⟩ − V^μ_t(s)]`.

**Formalization Note** 0-based layers (`t ∈ Finset.range H` is the paper's `t = 1, …, H`);
`d^π_t` is `stateLaw M π t` (started from `ρ = M.d1`), `J` is `totalCost`, and `V`, `Q` are the
published value and action-value functions with cost `ℓ_t = M.R t`. -/
theorem lemma_3_3 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (π μ : Policy S A H) (hπ : IsPolicy H π) (hμ : IsPolicy H μ) :
    totalCost M π - totalCost M μ =
      ∑ t ∈ Finset.range H, ∑ s : S,
        stateLaw M π t s * ((∑ a : A, Q M μ t s a * π t s a) - V M μ t s) := by sorry

end AuditAdapt
