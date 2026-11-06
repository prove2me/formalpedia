-- Prove2me | Theorems.Thm_BorelRobustMDP_corollary_3_9
-- name    : BorelRobustMDP.corollary_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:11.382222+00:00
-- url     : https://prove2.me/theorems/b42c0c6a-46f0-4411-a229-c64b39eecc43
-- title:
--   Corollary 3.9 — robust value iteration for a Markov policy
-- statement:
--   Let Assumptions 2.1 and 3.1 hold, and let $\pi=(d_0,\dots,d_{N-1})\in\Pi^M$. For $n=0,\dots,N$ and $h_n\in\mathcal H_n$ one has $J_{n\pi}(x_n)=V_{n\pi}(h_n)$, and
--
--   $$J_{n\pi}(x)=\sup_{Q\in\mathcal Q_{n+1}}\int c_n(x,d_n(x),T_n(x,d_n(x),Z_{n+1}))+J_{n+1\pi}(T_n(x,d_n(x),Z_{n+1}))\,dQ=\mathcal T_{nd_n}J_{n+1\pi}(x).$$
--
--   Moreover, for every $\epsilon>0$ there is a Markovian $\epsilon$-optimal policy of nature, and if the ambiguity sets are all weak* closed there is a Markovian optimal policy of nature.
--
--   So against a Markov controller, nature loses nothing by being Markov.
--
--   **Formalization Note.** An $\epsilon$-optimal policy of nature is a single sequence $\gamma\in\Gamma^M$ with $J_{n\pi\gamma}(x)\ge J_{n\pi}(x)-\epsilon$ for all $n$ and $x$; an optimal one has equality with $\epsilon=0$. In the first clause $\pi$ is embedded in $\Pi^R$ by Dirac kernels.
--
--   Differences from the source:
--   - reading: the statement names no assumption → Assumptions 2.1 and 3.1 are hypotheses; reason: the corollary follows from Theorem 3.6, whose assumptions are standing in this part of the section
--   - reading: Markovian ϵ-optimal policy of nature → for every ϵ > 0 one sequence γ ∈ Γ^M with J_{nπ} − ϵ ≤ J_{nπγ} for all n and x, and with equality to J_{nπ} when closed; reason: the proof constructs the policy as in Theorem 3.6
--   - encoding: the Ionescu-Tulcea law (2.4) and conditional expectations E^{πγ}_{nh_n} → the forward composition pathLaw with Measure.bind, continued from h_n; V and J are Bochner integrals, and the suprema and infima are real ones over the types of policies; reason: this is the same finite-horizon measure; well-definedness and boundedness are Lemma 3.3
--   - encoding: feasible histories 𝓗_n, with policies and rules of nature defined on them → the raw history space Hist E A n with the predicate Feasible; kernels and rules are defined on raw histories, and statements are at feasible ones; reason: 𝓗_n is measurable, so kernels and rules extend, and a path from a feasible history stays feasible almost surely
--   - encoding: Assumption 3.1: there exist α, ϵ̲, ϵ̄, b̲, b̄, K; expectation inequalities; the closed ball B_ϵ(x̄, ā) → the data B : BoundingData, with the theorem for every such data; lower Lebesgue integrals of the nonnegative parts; a neighbourhood U of (x̄, ā); reason: for all data implies the existence form; the integrals are the same with integrability carried; closed balls of a compatible metric are a neighbourhood base
--   - reading: Assumption 3.1 (iii): E|dQ/dP_n|^q ≤ K → ‖dQ/dP_n‖_{L^q} ≤ K; reason: the printed form has no meaning at q = ∞; the proof of Lemma 2.3, p.23, uses the norm; for q < ∞ the two give the same existence of K
--   - encoding: σ(L^q, L^p) on the densities 𝒬_n^d and its Borel σ-algebra → the topology on 𝒬_n induced by Q ↦ ∫ f dQ for f ∈ L^p(P_n), with borel of it; weak* closed means closed in this topology on 𝓜^q(P_n); reason: ∫ f dQ = E[f dQ/dP_n], and 𝓜^q(P_n) is weak* closed in L^q, so these are the same notions; no Lp–Lq duality is needed to state them
--   - encoding: decision rule γ_n : 𝓗_n × A → 𝒬_{n+1}, and Markov rule γ_n : D_n → 𝒬_{n+1} → measurable maps on Hist E A n × A and on E × A, into the type R.Amb (n + 1); reason: the proof of Lemma 2.4, p.24, uses this measurability; a rule extends by a constant from a measurable set
--   - encoding: E and A are Borel spaces → metrizable second countable spaces with Borel σ-algebra that is standard Borel, in one universe; reason: this is a Borel subset of a Polish space; one universe is forced by the platform's Hist E A n
--   - encoding: T_n and c_n are defined on D_n × Z and D_n × E, with their continuity on those sets → total measurable functions on (E × A) × Z and (E × A) × E, with ContinuousOn and LowerSemicontinuousOn on D_n and D_n × E; reason: D_n is measurable, so every paper model extends by a constant, and only values on D_n enter a statement
--   - encoding: stages n = 0, …, N − 1 and ambiguity sets n = 1, …, N → ℕ-indexed families used at n < N and at 1 ≤ n ≤ N, and Fin N for the rules of a policy; N = 0 is not excluded; reason: the other indices are unused, and N = 0 is a harmless empty case
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, Corollary 3.9, p.10

import Mathlib
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BorelRobustMDP_Assumption21
import Definitions.Def_BorelRobustMDP_Assumption31
import Definitions.Def_BorelRobustMDP_value
import Definitions.Def_BorelRobustMDP_markovValue
import Definitions.Def_BorelRobustMDP_markovOperators

open MDPFinance.Bellman (Hist histState)

namespace BorelRobustMDP

universe u v

/-- Corollary 3.9 (Bäuerle & Glauner, arXiv:2007.13103v1, p.10). Under Assumptions 2.1 and 3.1, for
`π = (d_0, …, d_{N−1}) ∈ Π^M`: `J_{nπ}(x_n) = V_{nπ}(h_n)` for `n = 0, …, N`; the robust value iteration
`J_{nπ}(x) = sup_{Q∈𝒬_{n+1}} ∫ c_n(x, d_n(x), T_n(x, d_n(x), Z_{n+1})) + J_{n+1π}(T_n(x, d_n(x), Z_{n+1})) dQ
= 𝒯_{nd_n} J_{n+1π}(x)` holds; for every `ϵ > 0` there is a Markovian `ϵ`-optimal policy of nature,
and if the ambiguity sets are weak* closed a Markovian optimal one.

**Formalization Note.** The Assumptions are the standing ones of the corollary, whose proof rests on
Theorem 3.6. `V_{nπ}` is the robust value of `π` embedded in `Π^R` by Dirac kernels. An
`ϵ`-optimal policy of nature is one sequence `γ`, with `J_{nπ}(x) − ϵ ≤ J_{nπγ}(x)` for all `n`, `x`. -/
theorem corollary_3_9 {E A : Type u} {Z : Type v} [TopologicalSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [StandardBorelSpace E]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A] [MeasurableSpace Z] {N : ℕ}
    (R : RobustModel E A Z N) (B : BoundingData E) (h21 : Assumption21 R.toDecisionModel)
    (h31 : Assumption31 R B) (d : MarkovPolicy R.toDecisionModel) :
    (∀ n ≤ N, ∀ h : Hist E A n, R.Feasible n h →
      markovRobustValue R d n (histState n h) = robustValue R d.toPolicy n h) ∧
    (∀ n : Fin N, ∀ x,
      markovRobustValue R d n x =
          (⨆ Q : R.Amb (n + 1),
            ∫ z, R.c n (x, d.rule n x) (R.T n (x, d.rule n x) z) +
              markovRobustValue R d (n + 1) (R.T n (x, d.rule n x) z) ∂Q.measure) ∧
      markovRobustValue R d n x = Td R n (markovRobustValue R d (n + 1)) (d.rule n) x) ∧
    (∀ ε : ℝ, 0 < ε → ∃ γ : MarkovNature R, ∀ n ≤ N, ∀ x,
      markovRobustValue R d n x - ε ≤ markovValue R d γ n x) ∧
    ((∀ n, 1 ≤ n → n ≤ N → R.WeakStarClosed n) →
      ∃ γ : MarkovNature R, ∀ n ≤ N, ∀ x, markovValue R d γ n x = markovRobustValue R d n x) := by sorry

end BorelRobustMDP
