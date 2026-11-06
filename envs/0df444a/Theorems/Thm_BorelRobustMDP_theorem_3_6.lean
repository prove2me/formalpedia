-- Prove2me | Theorems.Thm_BorelRobustMDP_theorem_3_6
-- name    : BorelRobustMDP.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:49.611825+00:00
-- url     : https://prove2.me/theorems/f979b085-8869-4971-9e81-f1fda8dd5993
-- title:
--   Theorem 3.6 — the robust value $V_{n\pi}$ of a policy: measurability, cost iteration, nature's response
-- statement:
--   Let Assumptions 2.1 and 3.1 hold, and let $\pi\in\Pi^R$.
--
--   1. The robust value $V_{n\pi}$ is a measurable function of $h_n\in\mathcal H_n$ for $n=0,\dots,N-1$, and $V_{N\pi}(h_N)=c_N(x_N)$, $V_{n\pi}(h_n)=\mathcal T_{n\pi_n}V_{n+1\pi}(h_n)$.
--   2. If the ambiguity sets are weak* closed, there exist maximizing decision rules $\gamma_n^*$ of nature for all $n$, and each sequence of such rules $\gamma^*\in\Gamma$ is an optimal response of nature to $\pi$: $V_{n\pi}=V_{n\pi\gamma^*}$ for $n=0,\dots,N-1$.
--
--   Part 1 has no closedness hypothesis: a norm-bounded ambiguity set may fail to attain its suprema, and the supremum still moves inside the integral.
--
--   **Formalization Note.** Measurability is on the subtype of feasible histories. A maximizing rule attains the inner supremum of $\mathcal T_{n\pi_n}V_{n+1\pi}$ at every feasible $h_n$ and $a\in D_n(x_n)$.
--
--   Differences from the source:
--   - reading: γ* = (γ*_1, …, γ*_{N−1}) → γ* = (γ*_0, …, γ*_{N−1}); reason: the rules exist for all n, and an element of Γ starts at time 0
--   - reading: maximizing decision rules → rules attaining the supremum of the inner integral with v = V_{n+1π} at every feasible h_n and a ∈ D_n(x_n); reason: this is the maximizer at (3.1) in the proof
--   - encoding: measurable function of h_n ∈ 𝓗_n → Measurable on the subtype of feasible histories; reason: 𝓗_n carries the trace σ-algebra; off it the total extensions are arbitrary
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
--   Bäuerle & Glauner, arXiv:2007.13103v1, Theorem 3.6, p.8

import Mathlib
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BorelRobustMDP_Assumption21
import Definitions.Def_BorelRobustMDP_Assumption31
import Definitions.Def_BorelRobustMDP_value
import Definitions.Def_BorelRobustMDP_histOperators

open MDPFinance.Bellman (Hist histState)

namespace BorelRobustMDP

universe u v

/-- Theorem 3.6 (Bäuerle & Glauner, arXiv:2007.13103v1, p.8). Under Assumptions 2.1 and 3.1, for
`π ∈ Π^R`:

a) the robust value `V_{nπ}` is a measurable function of `h_n ∈ 𝓗_n`, `n < N`, with
`V_{Nπ}(h_N) = c_N(x_N)` and `V_{nπ}(h_n) = 𝒯_{nπ_n} V_{n+1π}(h_n)`;

b) if the ambiguity sets are weak* closed, maximizing decision rules `γ*_n` of nature exist for all
`n`, and each sequence of them is an optimal response: `V_{nπ} = V_{nπγ*}`, `n < N`.

**Formalization Note.** Part a) has no closedness hypothesis. Measurability is on the subtype of
feasible histories: off `𝓗_n` the total extensions of `T`, `c` are arbitrary. The printed
`γ* = (γ*_1, …)` is read as starting at `γ*_0`. -/
theorem theorem_3_6 {E A : Type u} {Z : Type v} [TopologicalSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [StandardBorelSpace E]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A] [MeasurableSpace Z] {N : ℕ}
    (R : RobustModel E A Z N) (B : BoundingData E) (h21 : Assumption21 R.toDecisionModel)
    (h31 : Assumption31 R B) (π : Policy R.toDecisionModel) :
    ((∀ n < N, Measurable fun h : {h : Hist E A n // R.Feasible n h} => robustValue R π n h.1) ∧
      (∀ h : Hist E A N, R.Feasible N h → robustValue R π N h = R.cN (histState N h)) ∧
      ∀ n < N, ∀ h : Hist E A n, R.Feasible n h →
        robustValue R π n h = histTp R π n (robustValue R π (n + 1)) h) ∧
    ((∀ n, 1 ≤ n → n ≤ N → R.WeakStarClosed n) →
      (∀ n : Fin N, ∃ g : Hist E A n × A → R.Amb (n + 1),
        Measurable g ∧ IsHistMaximizer R n (robustValue R π (n + 1)) g) ∧
      ∀ γ : NaturePolicy R,
        (∀ n : Fin N, IsHistMaximizer R n (robustValue R π (n + 1)) (γ.rule n)) →
        ∀ n < N, ∀ h : Hist E A n, R.Feasible n h → robustValue R π n h = value R π γ n h) := by sorry

end BorelRobustMDP
