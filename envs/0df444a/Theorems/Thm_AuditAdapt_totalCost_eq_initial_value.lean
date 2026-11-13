-- Prove2me | Theorems.Thm_AuditAdapt_totalCost_eq_initial_value
-- name    : AuditAdapt.totalCost_eq_initial_value
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:03:50.591523+00:00
-- url     : https://prove2.me/theorems/692da2d7-8b87-4566-90a9-f3a9fabbccf8
-- title:
--   Proof of Lemma 3.3, p.3 — $J(\mu)=\mathbb E_{s_1\sim\rho}V^\mu_1(s_1)$
-- statement:
--   Let $\mu$ be a Markov policy in a finite-horizon MDP with initial law $\rho$. Its expected total cost equals its initial value averaged over the initial state:
--
--   $$
--   J(\mu)=\mathbb E^\mu\Big[\sum_{t=1}^H\ell_t(s_t,a_t)\Big]=\sum_{s\in\mathcal S}\rho(s)\,V^\mu_1(s).
--   $$
--
--   The proof of Lemma 3.3 telescopes $\sum_{t=1}^H\big(\ell_t(s_t,a_t)+V^\mu_{t+1}(s_{t+1})-V^\mu_t(s_t)\big)=\sum_t\ell_t(s_t,a_t)-V^\mu_1(s_1)$ and reads the expectation of the right side as $J(\pi)-J(\mu)$; that reading is this identity. It links the forward description of $J$ (through the state laws) to the backward one (through the value function).
--
--   Differences from the source:
--   - encoding: steps t = 1, …, H and the terminal convention V^μ_{H+1} ≡ 0 → 0-based layers t ∈ Finset.range H, terminal V M μ H = 0; reason: index shift only (layer t is the paper's step t + 1)
--   - encoding: Markov policy π = (π_t)_{t≤H} with π_t(· | s) ∈ Δ(A) → π : ℕ → S → A → ℝ with IsPolicy H π (a distribution at every layer < H and every state); reason: values at layers ≥ H are never used; same instances
--   - encoding: kernels P_t(· | s, a) ∈ Δ(S) for t ≤ H → EpisodicMDP field P h, a distribution for every h ∈ ℕ (P_sum_one); reason: kernels beyond the horizon are never used; every paper MDP extends (repeat P_H)
--   - encoding: bounded costs ℓ_t : S × A → ℝ → EpisodicMDP field R t, an arbitrary real function (documented on the platform as a mean reward); reason: S and A are finite, so every real function is bounded; R is used as the cost with no sign change
--   - encoding: J(π) = E^π[Σ_t ℓ_t(s_t, a_t)] → totalCost M π = Σ_t Σ_s d^π_t(s) Σ_a π_t(a | s) ℓ_t(s, a); reason: linearity of expectation over the law P_t(s,a) = d^π_t(s) π_t(a | s) of (s_t, a_t); same value
-- source:
--   Aldridge, Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing Adaptive Policies, STOC 2027 submission (held version, sha256 3f6ad545b0454d8de6836d32bb81359da5022bbc373510a7c75452ab66ec9fc2), proof of Lemma 3.3, p.3

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_AuditAdapt_stateLaw
import Definitions.Def_AuditAdapt_totalCost

namespace AuditAdapt

open FoundationsRL.RLBasics

/-- **Proof of Lemma 3.3, p.3: `J(μ) = E_{s_1∼ρ}[V^μ_1(s_1)]`** (Aldridge, *Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing
Adaptive Policies*, STOC 2027 submission (held version, sha256 3f6ad545…)). The expected
total cost of a Markov policy, computed forward from its state laws, equals the initial value
averaged over `s_1 ∼ ρ`. (The proof of Lemma 3.3 telescopes `∑_t (ℓ_t + V^μ_{t+1}(s_{t+1}) − V^μ_t(s_t))
= ∑_t ℓ_t − V^μ_1(s_1)` and reads the expectation of the right side as `J(π) − J(μ)`; this is the
identification of `E_ρ V^μ_1` with `J(μ)` it uses.)

**Formalization Note** 0-based layers: `V M μ 0` is the paper's `V^μ_1`; `ρ` is `M.d1`. -/
theorem totalCost_eq_initial_value {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (μ : Policy S A H) (hμ : IsPolicy H μ) :
    totalCost M μ = ∑ s : S, M.d1 s * V M μ 0 s := by sorry

end AuditAdapt
