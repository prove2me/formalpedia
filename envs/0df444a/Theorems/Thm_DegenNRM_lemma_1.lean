-- Prove2me | Theorems.Thm_DegenNRM_lemma_1
-- name    : DegenNRM.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:35:37.590096+00:00
-- url     : https://prove2.me/theorems/56366cc4-252c-4534-b19a-36db3a2a4275
-- title:
--   Lemma 1 — the regret of a feasible policy is at most the sum of its myopic terms
-- statement:
--   Let $\bar V_c(I_t)$ be any function of the period $t\in\{1,\dots,T+1\}$, the remaining capacity $c$ and the sample path, playing the role of a relaxation of the prophet's reward from period $t$ on, such that
--
--   1. $\bar V_c(I_{T+1})=0$ for every $c$;
--   2. $\mathbb E_{I}[V^{\mathrm{off}}(I)]\le\mathbb E_I[\bar V_C(I_1)]$, inequality (6).
--
--   Then for every feasible (possibly randomized) online policy $\pi$ with remaining capacities $\tilde c^\pi_t$ and decisions $\tilde x^\pi_t$,
--   $$\mathrm{Regret}(\pi)=\mathbb E[V^{\mathrm{off}}(I)]-\mathbb E[V^\pi(I)]\le\sum_{t=1}^T\mathbb E\Big[\bar V_{\tilde c^\pi_t}(I_t)-\bar V_{\tilde c^\pi_t-\tilde a_t\tilde x^\pi_t}(I_{t+1})-\tilde r_t\tilde x^\pi_t\Big],$$
--   the sum over $t$ of the myopic terms $\mathrm{Myopic}_t(\pi,\tilde c^\pi_t)$ of (8) at the random capacities.
--
--   This decomposition reduces the regret bound to a per-period bound on the myopic regret, which Lemmas 5–7 provide for the semi-fluid relaxation.
--
--   **Formalization Note** The expectations are over the policy's randomness and the sample path; the statement assumes the integrability of $V^{\mathrm{off}}$, of each $\bar V_{\tilde c^\pi_t}(I_t)$ and of each $\tilde r_t\tilde x^\pi_t$.
--
--   Differences from the source:
--
--   - encoding: m resources, n query types; query t has size ã_t ∈ A = {a_1,…,a_n} and reward r̃_t, and the type j_t is observed → resources Fin m, types Fin n; an arrival is (j, r) ∈ Fin n × ℝ with size a_j, the law of an arrival is Σ_j p_j (δ_j ⊗ F_j), and periods t ∈ [T] are the coordinates t − 1 of a path in (Fin n × ℝ)^T; reason: reading R3 of the mission (Algorithm 2 takes the type j_t as input, p.15); same instances
--   - encoding: p_j = P(ã = a_j) for the support A = {a_1,…,a_n} → p_j > 0 and Σ_j p_j = 1; reason: a support point has positive probability and κ₁ of (15) divides by p_j; this excludes only undefined cases
--   - generalization: Section 3's standing Assumption 1 (p.10) → not assumed; reason: the telescoping argument (7)–(8) does not use it; the statement under Assumption 1 is an instance
--   - generalization: a relaxation V̄_c(I_t) of the prophet from period t on (decisions x_τ ∈ [0,1]) → any function V̄ of (t, c, sample path) with V̄_c(I_{T+1}) = 0 and E V̄_C(I_1) ≥ E V^off; reason: the proof uses only these two properties; the paper's relaxations are instances
--   - reading: E_{c̃^π_t}[Myopic_t(π, c̃^π_t)] with Myopic_t(π, c) of (8) at a fixed c → the expectation of the myopic integrand of (8) at the random state c̃^π_t; reason: reading R7: (8) at a fixed c is meaningful only for state-feedback policies; the proof (p.11) telescopes the integrand
--   - encoding: a randomized policy (p.6: 'x̃^π_t can be stochastic') → decisions x_t(ξ, I) with internal randomness ξ from an independent probability space; reason: covers every randomized policy; deterministic policies take a one-point space
--   - encoding: the expectations of (6)–(8) → integrability of V^off, of V̄ at the random capacities and of r̃_t x̃_t as hypotheses; reason: the expectations the paper writes must exist; for the semi-fluid relaxation they are bounded
-- source:
--   Jiang, Ma & Zhang, Degeneracy is OK: Logarithmic Regret for Network Revenue Management with Indiscrete Distributions, arXiv:2210.07996v5, Lemma 1, p.11; (6)–(8), p.11

import Mathlib
import Definitions.Def_DegenNRM_arrivalLaw
import Definitions.Def_DegenNRM_offlineValue
import Definitions.Def_DegenNRM_FeasiblePolicy

open MeasureTheory

namespace DegenNRM

/-- **Lemma 1** (Jiang, Ma & Zhang, arXiv:2210.07996v5, Lemma 1, p.11; with (6)–(8), p.11).

Let `V̄_c(I_t)` be any relaxation of the prophet's reward from period `t` on, given remaining
capacity `c`, with `V̄_c(I_{T+1}) = 0` for every `c` and `E[V̄_C(I_1)] ≥ E[V^off(I)]` (6). Then for
any feasible online policy `π`,

`Regret(π) ≤ Σ_{t=1}^T E[ V̄_{c̃_t}(I_t) - V̄_{c̃_t - ã_t x̃_t}(I_{t+1}) - r̃_t x̃_t ]`,

the sum over `t` of the myopic terms `Myopic_t(π, c̃^π_t)` of (8) at the random capacities.

**Formalization Note.** `Vbar k c ω` is `V̄_c(I_{k+1})` (so `Vbar 0` is `V̄(I_1)` and
`Vbar T` is `V̄(I_{T+1})`); the statement holds for every such function, whatever its
dependence on `ω`. `E_{c̃_t}[Myopic_t(π, c̃_t)]` is read as the expectation of the myopic
integrand at the random state `c̃^π_t` (reading R7). Expectations over the policy's randomness
and the sample path are integrals against `ν ⊗ P`; the integrability hypotheses make them the
expectations the paper writes. -/
theorem lemma_1 {m n T : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (inst : Instance m n)
    (C : Fin m → ℝ) (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (x : Fin T → Ξ → (Fin T → Fin n × ℝ) → Bool) (hx : IsFeasiblePolicy inst C x)
    (Vbar : ℕ → (Fin m → ℝ) → (Fin T → Fin n × ℝ) → ℝ)
    (hVbar_end : ∀ c ω, Vbar T c ω = 0)
    (h6 : ∫ ω, offlineValue inst C ω ∂(pathLaw inst T) ≤ ∫ ω, Vbar 0 C ω ∂(pathLaw inst T))
    (hint_off : Integrable (offlineValue inst C) (pathLaw inst T))
    (hint_V : ∀ k, k ≤ T → Integrable
      (fun p : Ξ × (Fin T → Fin n × ℝ) => Vbar k (policyCapacity inst C x k p.1 p.2) p.2)
      (ν.prod (pathLaw inst T)))
    (hint_r : ∀ t : Fin T, Integrable
      (fun p : Ξ × (Fin T → Fin n × ℝ) => if x t p.1 p.2 then (p.2 t).2 else 0)
      (ν.prod (pathLaw inst T))) :
    (∫ ω, offlineValue inst C ω ∂(pathLaw inst T)) -
        ∫ p, policyTotal x p.1 p.2 ∂(ν.prod (pathLaw inst T)) ≤
      ∑ t : Fin T, ∫ p : Ξ × (Fin T → Fin n × ℝ),
        (Vbar t (policyCapacity inst C x t p.1 p.2) p.2
          - Vbar ((t : ℕ) + 1) (policyCapacity inst C x t p.1 p.2 -
              (if x t p.1 p.2 then inst.a (p.2 t).1 else 0)) p.2
          - (if x t p.1 p.2 then (p.2 t).2 else 0)) ∂(ν.prod (pathLaw inst T)) := by sorry

end DegenNRM
