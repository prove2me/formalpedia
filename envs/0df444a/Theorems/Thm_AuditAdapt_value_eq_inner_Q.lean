-- Prove2me | Theorems.Thm_AuditAdapt_value_eq_inner_Q
-- name    : AuditAdapt.value_eq_inner_Q
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T05:58:18.347325+00:00
-- url     : https://prove2.me/theorems/b4132bcf-2a18-4ed1-82c8-473856e1b270
-- title:
--   §2, p.3 — $Q^\mu_t=\ell_t+\mathbb E\,V^\mu_{t+1}$, $V^\mu_t=\langle Q^\mu_t,\mu_t\rangle$, $V^\mu_{H+1}\equiv0$
-- statement:
--   Let $\mu$ be a Markov policy in a finite-horizon MDP with costs $\ell_t$ and kernels $P_t$. Its action-value and value functions satisfy, for every $t=1,\dots,H$, every $s\in\mathcal S$ and every $a\in\mathcal A$,
--
--   $$
--   Q^\mu_t(s,a)=\ell_t(s,a)+\mathbb E_{s'\sim P_t(\cdot\mid s,a)}\big[V^\mu_{t+1}(s')\big],\qquad V^\mu_t(s)=\langle Q^\mu_t(s,\cdot),\mu_t(\cdot\mid s)\rangle,\qquad V^\mu_{H+1}\equiv0 .
--   $$
--
--   These are the paper's defining equations for $Q^\mu$ and $V^\mu$. The proof of Theorem 3.4 uses the second one for the open-loop marginal: $V^\nu_t(s)=\langle Q^\nu_t(s,\cdot),\bar p_t\rangle$.
--
--   **Formalization Note** The published value function `V` of `FoundationsRL.RLBasics` is defined by a backward recursion with the policy's action probabilities outside the bracket; this theorem identifies it with the paper's definition through the published `Q`.
--
--   Differences from the source:
--   - encoding: steps t = 1, …, H and the terminal convention V^μ_{H+1} ≡ 0 → 0-based layers t ∈ Finset.range H, terminal V M μ H = 0; reason: index shift only (layer t is the paper's step t + 1)
--   - encoding: Markov policy π = (π_t)_{t≤H} with π_t(· | s) ∈ Δ(A) → π : ℕ → S → A → ℝ with IsPolicy H π (a distribution at every layer < H and every state); reason: values at layers ≥ H are never used; same instances
--   - encoding: kernels P_t(· | s, a) ∈ Δ(S) for t ≤ H → EpisodicMDP field P h, a distribution for every h ∈ ℕ (P_sum_one); reason: kernels beyond the horizon are never used; every paper MDP extends (repeat P_H)
--   - encoding: bounded costs ℓ_t : S × A → ℝ → EpisodicMDP field R t, an arbitrary real function (documented on the platform as a mean reward); reason: S and A are finite, so every real function is bounded; R is used as the cost with no sign change
-- source:
--   Aldridge, Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing Adaptive Policies, STOC 2027 submission (held version, sha256 3f6ad545b0454d8de6836d32bb81359da5022bbc373510a7c75452ab66ec9fc2), §2 "MDPs and policies", p.3

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core

namespace AuditAdapt

open FoundationsRL.RLBasics

/-- **§2, p.3: the value and action-value functions** (Aldridge, *Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing
Adaptive Policies*, STOC 2027 submission (held version, sha256 3f6ad545…)):
`Q^μ_t(s,a) = ℓ_t(s,a) + E_{s'∼P_t(·|s,a)}[V^μ_{t+1}(s')]`, `V^μ_t(s) = ⟨Q^μ_t(s,·), μ_t(·|s)⟩`,
`V^μ_{H+1} ≡ 0`, for a Markov policy `μ`, stated for the published `V` and `Q`.

**Formalization Note** The published `V` is defined by a backward recursion (`valueAux`); this
theorem identifies it with the paper's definition. 0-based layers: `t < H` is the paper's
`t = 1, …, H`, and `V M μ H` is the paper's `V^μ_{H+1}`. The cost `ℓ_t` is `M.R t`. -/
theorem value_eq_inner_Q {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (μ : Policy S A H) (hμ : IsPolicy H μ) :
    (∀ t, t < H → ∀ s : S, ∀ a : A,
        Q M μ t s a = M.R t s a + ∑ s' : S, M.P t s a s' * V M μ (t + 1) s') ∧
    (∀ t, t < H → ∀ s : S, V M μ t s = ∑ a : A, Q M μ t s a * μ t s a) ∧
    (∀ s : S, V M μ H s = 0) := by sorry

end AuditAdapt
