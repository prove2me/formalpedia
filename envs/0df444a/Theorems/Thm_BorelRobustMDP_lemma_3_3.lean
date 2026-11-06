-- Prove2me | Theorems.Thm_BorelRobustMDP_lemma_3_3
-- name    : BorelRobustMDP.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:50.899012+00:00
-- url     : https://prove2.me/theorems/0f83a540-3de6-4077-a6a3-8447cab60eec
-- title:
--   Lemma 3.3 — the two-sided bound on $V_{n\pi\gamma}$
-- statement:
--   Under Assumption 3.1, for all policy pairs $(\pi,\gamma)\in\Pi^R\times\Gamma$, times $n=0,\dots,N$ and histories $h_n\in\mathcal H_n$, the law of motion continuing $h_n$ is a probability measure, the total cost is integrable under it, and
--
--   $$\frac{1-\alpha^{N+1-n}}{1-\alpha}\,\underline b(x_n)\le V_{n\pi\gamma}(h_n)\le\frac{1-\alpha^{N+1-n}}{1-\alpha}\,\overline b(x_n).$$
--
--   So the value (2.5) of every policy pair is well-defined, and bounded uniformly in the policies.
--
--   Differences from the source:
--   - generalization: the two inequalities, with well-definedness claimed in the text on p.6 → the two inequalities, and clauses stating that the law is a probability measure and the cost integrable; reason: this only adds clauses, which rule out a junk value 0
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
--   Bäuerle & Glauner, arXiv:2007.13103v1, Lemma 3.3, p.7, and the paragraph before it, p.6

import Mathlib
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BorelRobustMDP_Assumption31
import Definitions.Def_BorelRobustMDP_value

open MeasureTheory
open MDPFinance.Bellman (Hist histState)

namespace BorelRobustMDP

universe u v

/-- Lemma 3.3 (Bäuerle & Glauner, arXiv:2007.13103v1, p.7). For all policy pairs `(π, γ) ∈ Π^R × Γ`,
times `n = 0, …, N` and histories `h_n ∈ 𝓗_n`:
`(1 − α^{N+1−n})/(1 − α) · b̲(x_n) ≤ V_{nπγ}(h_n) ≤ (1 − α^{N+1−n})/(1 − α) · b̄(x_n)`.

**Formalization Note.** The first two clauses are the well-definedness claimed before the lemma
(p.6): the law of motion is a probability measure and the cost is integrable under it. Without them a
junk value `0` could satisfy the bounds. -/
theorem lemma_3_3 {E A : Type u} {Z : Type v} [TopologicalSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [StandardBorelSpace E]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A] [MeasurableSpace Z] {N : ℕ}
    (R : RobustModel E A Z N) (B : BoundingData E) (h31 : Assumption31 R B)
    (π : Policy R.toDecisionModel) (γ : NaturePolicy R) (n : ℕ) (hn : n ≤ N) (h : Hist E A n)
    (hh : R.Feasible n h) :
    IsProbabilityMeasure (law R π γ n h (N - n)) ∧
      Integrable (totalCost R n n (N - n)) (law R π γ n h (N - n)) ∧
      (1 - B.α ^ (N + 1 - n)) / (1 - B.α) * B.blo (histState n h) ≤ value R π γ n h ∧
      value R π γ n h ≤ (1 - B.α ^ (N + 1 - n)) / (1 - B.α) * B.bhi (histState n h) := by sorry

end BorelRobustMDP
