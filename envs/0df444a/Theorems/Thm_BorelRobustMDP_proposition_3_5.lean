-- Prove2me | Theorems.Thm_BorelRobustMDP_proposition_3_5
-- name    : BorelRobustMDP.proposition_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:48.826355+00:00
-- url     : https://prove2.me/theorems/26b9f480-26b4-4fc4-9f17-f9ceedad7f18
-- title:
--   Proposition 3.5 — the cost iteration $V_{n\pi\gamma}=\mathcal T_{n\pi_n\gamma_n}V_{n+1\pi\gamma}$
-- statement:
--   Under Assumption 3.1, the value of a policy pair $(\pi,\gamma)\in\Pi^R\times\Gamma$ can be calculated recursively for $n=0,\dots,N$ and $h_n\in\mathcal H_n$:
--
--   $$V_{N\pi\gamma}(h_N)=c_N(x_N),\qquad V_{n\pi\gamma}(h_n)=\mathcal T_{n\pi_n\gamma_n}V_{n+1\pi\gamma}(h_n).$$
--
--   This links the value, defined from the law of motion, to the operators.
--
--   Differences from the source:
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
--   Bäuerle & Glauner, arXiv:2007.13103v1, Proposition 3.5, p.8

import Mathlib
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BorelRobustMDP_Assumption31
import Definitions.Def_BorelRobustMDP_value
import Definitions.Def_BorelRobustMDP_histOperators

open MDPFinance.Bellman (Hist histState)

namespace BorelRobustMDP

universe u v

/-- Proposition 3.5 (Bäuerle & Glauner, arXiv:2007.13103v1, p.8). Under Assumption 3.1 the value of a
policy pair `(π, γ)` is computed recursively: `V_{Nπγ}(h_N) = c_N(x_N)` and
`V_{nπγ}(h_n) = 𝒯_{nπ_nγ_n} V_{n+1πγ}(h_n)`.

**Formalization Note.** `value` is the expectation under the law of motion and `histTpg` the operator of
Definition 3.4, so this is a statement about two different objects. -/
theorem proposition_3_5 {E A : Type u} {Z : Type v} [TopologicalSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [StandardBorelSpace E]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A] [MeasurableSpace Z] {N : ℕ}
    (R : RobustModel E A Z N) (B : BoundingData E) (h31 : Assumption31 R B)
    (π : Policy R.toDecisionModel) (γ : NaturePolicy R) :
    (∀ h : Hist E A N, R.Feasible N h → value R π γ N h = R.cN (histState N h)) ∧
      ∀ n < N, ∀ h : Hist E A n, R.Feasible n h →
        value R π γ n h = histTpg R π γ n (value R π γ (n + 1)) h := by sorry

end BorelRobustMDP
