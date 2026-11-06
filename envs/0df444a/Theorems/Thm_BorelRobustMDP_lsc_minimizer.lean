-- Prove2me | Theorems.Thm_BorelRobustMDP_lsc_minimizer
-- name    : BorelRobustMDP.lsc_minimizer
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:23.991206+00:00
-- url     : https://prove2.me/theorems/28d55428-e144-429b-a38d-8d54ba2003f2
-- title:
--   Proof of Theorem 3.10, p.11 — a minimizing Markov decision rule exists and $\mathcal T_nv$ is lower semicontinuous
-- statement:
--   Under Assumptions 2.1 and 3.1, for every $v\in\mathbb B$ and $n<N$, the function $\mathcal T_nv$ is lower semicontinuous and there is a Markov decision rule $d$ with
--
--   $$\sup_{Q\in\mathcal Q_{n+1}}L_nv(x,d(x),Q)=\mathcal T_nv(x)\quad\text{for all }x\in E.$$
--
--   This is the application of Proposition 2.4.3 of Bäuerle–Rieder in the proof of Theorem 3.10.
--
--   Differences from the source:
--   - generalization: v = J_{n+1} → every v ∈ 𝔹; reason: the proof's hypotheses are shown for every v ∈ 𝔹, and J_{n+1} ∈ 𝔹 in the induction, so this specializes to the paper's claim
--   - encoding: Assumption 3.1: there exist α, ϵ̲, ϵ̄, b̲, b̄, K; expectation inequalities; the closed ball B_ϵ(x̄, ā) → the data B : BoundingData, with the theorem for every such data; lower Lebesgue integrals of the nonnegative parts; a neighbourhood U of (x̄, ā); reason: for all data implies the existence form; the integrals are the same with integrability carried; closed balls of a compatible metric are a neighbourhood base
--   - reading: Assumption 3.1 (iii): E|dQ/dP_n|^q ≤ K → ‖dQ/dP_n‖_{L^q} ≤ K; reason: the printed form has no meaning at q = ∞; the proof of Lemma 2.3, p.23, uses the norm; for q < ∞ the two give the same existence of K
--   - encoding: σ(L^q, L^p) on the densities 𝒬_n^d and its Borel σ-algebra → the topology on 𝒬_n induced by Q ↦ ∫ f dQ for f ∈ L^p(P_n), with borel of it; weak* closed means closed in this topology on 𝓜^q(P_n); reason: ∫ f dQ = E[f dQ/dP_n], and 𝓜^q(P_n) is weak* closed in L^q, so these are the same notions; no Lp–Lq duality is needed to state them
--   - encoding: E and A are Borel spaces → metrizable second countable spaces with Borel σ-algebra that is standard Borel, in one universe; reason: this is a Borel subset of a Polish space; one universe is forced by the platform's Hist E A n
--   - encoding: T_n and c_n are defined on D_n × Z and D_n × E, with their continuity on those sets → total measurable functions on (E × A) × Z and (E × A) × E, with ContinuousOn and LowerSemicontinuousOn on D_n and D_n × E; reason: D_n is measurable, so every paper model extends by a constant, and only values on D_n enter a statement
--   - encoding: stages n = 0, …, N − 1 and ambiguity sets n = 1, …, N → ℕ-indexed families used at n < N and at 1 ≤ n ≤ N, and Fin N for the rules of a policy; N = 0 is not excluded; reason: the other indices are unused, and N = 0 is a harmless empty case
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, proof of Theorem 3.10, p.11, "yields the existence of a minimizing Markov decision rule"

import Mathlib
import Definitions.Def_BorelRobustMDP_Assumption21
import Definitions.Def_BorelRobustMDP_Assumption31
import Definitions.Def_BorelRobustMDP_Bb
import Definitions.Def_BorelRobustMDP_markovOperators

namespace BorelRobustMDP

universe u v

/-- A step of the proof of Theorem 3.10 (Bäuerle & Glauner, arXiv:2007.13103v1, p.11, "yields the
existence of a minimizing Markov decision rule"): for every `v ∈ 𝔹` and `n < N`, `𝒯_n v` is lower
semicontinuous and there is a Markov decision rule `d` attaining it at every state.

**Formalization Note.** The paper applies Proposition 2.4.3 of Bäuerle & Rieder to `v = J_{n+1}`,
after showing the lower semicontinuity for every `v ∈ 𝔹`; the statement here is for every `v ∈ 𝔹`. -/
theorem lsc_minimizer {E A : Type u} {Z : Type v} [TopologicalSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [StandardBorelSpace E]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A] [MeasurableSpace Z] {N : ℕ}
    (R : RobustModel E A Z N) (B : BoundingData E) (h21 : Assumption21 R.toDecisionModel)
    (h31 : Assumption31 R B) (v : E → ℝ) (hv : v ∈ BB B.b) (n : ℕ) (hn : n < N) :
    LowerSemicontinuous (Tmin R n v) ∧ ∃ d : E → A, IsMinimizer R n v d := by sorry

end BorelRobustMDP
