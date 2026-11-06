-- Prove2me | Theorems.Thm_BorelRobustMDP_theorem_3_10
-- name    : BorelRobustMDP.theorem_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:31.888212+00:00
-- url     : https://prove2.me/theorems/f5fbc1fb-78f5-46c1-9076-d93c1db5b041
-- title:
--   Theorem 3.10 — robust value iteration and deterministic Markov optimal policies for both players
-- statement:
--   Let $E$ and $A$ be Borel spaces, and let Assumptions 2.1 and 3.1 hold, for any $q\in(1,\infty]$.
--
--   **a)** For $n=0,\dots,N$, deterministic Markov policies suffice for both the controller and nature: $V_n(h_n)=J_n(x_n)$ for all $h_n\in\mathcal H_n$. Moreover $J_n\in\mathbb B$ and $J_n$ satisfies the Bellman equation
--
--   $$J_N(x)=c_N(x),\qquad J_n(x)=\mathcal T_nJ_{n+1}(x),\quad x\in E.$$
--
--   For $n=0,\dots,N-1$ there exist Markov minimizers $d_n^*$ of $J_{n+1}$, and every sequence of such minimizers is an optimal policy $\pi^*=(d_0^*,\dots,d_{N-1}^*)$ of the controller: $J_{n\pi^*}=J_n$ and $V_{n\pi^*}=V_n$ on $\mathcal H_n$.
--
--   **b)** If the ambiguity sets $\mathcal Q_n$ are weak* closed, then for every such $\pi^*$:
--
--   1. for each $n<N$ there is a measurable $\gamma_n^*:D_n\to\mathcal Q_{n+1}$ attaining $\sup_QL_nJ_{n+1}(x,a,Q)$ at every $(x,a)\in D_n$, and so $J_n=\mathcal T_{nd_n^*\gamma_n^*}J_{n+1}$;
--   2. every sequence $\gamma^*=(\gamma_0^*,\dots,\gamma_{N-1}^*)\in\Gamma^M$ with $J_n=\mathcal T_{nd_n^*\gamma_n^*}J_{n+1}$ for all $n<N$ is an optimal policy of nature: $J_n=J_{n\pi^*\gamma^*}$.
--
--   The theorem reduces a game over randomized history-dependent policies on Borel spaces, with unbounded cost and ambiguity sets that need not be closed, to a backward recursion over states.
--
--   Differences from the source:
--   - generalization: V_n = J_n and J_n ∈ 𝔹 for n = 0, …, N − 1 → n = 0, …, N; reason: at n = N both are c_N, as the first line of the proof says; this specializes to the printed range
--   - reading: T_{d*_nγ*_n} → 𝒯_{nd*_nγ*_n} of Definition 3.8; reason: the time index is missing from the print
--   - reading: there exist maximizing decision rules, i.e. J_n = T…, and every sequence of maximizers is optimal → existence for the stronger class of rules maximizing L_nJ_{n+1}(x, a, ·) at every (x, a) ∈ D_n, and every sequence of the weaker class with J_n = 𝒯_{nd*_nγ_n}J_{n+1}; reason: the phrase admits both classes; the stronger half of each clause implies the other reading
--   - reading: an optimal policy π* of the controller → J_{nπ*} = J_n for all n ≤ N and x, and V_{nπ*} = V_n at feasible histories, π* embedded in Π^R by Dirac kernels; reason: this is the meaning of (3.2) and of the optimization problem (2.6)
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
--   Bäuerle & Glauner, arXiv:2007.13103v1, Theorem 3.10, p.10; proof p.11

import Mathlib
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BorelRobustMDP_Assumption21
import Definitions.Def_BorelRobustMDP_Assumption31
import Definitions.Def_BorelRobustMDP_Bb
import Definitions.Def_BorelRobustMDP_value
import Definitions.Def_BorelRobustMDP_markovValue
import Definitions.Def_BorelRobustMDP_markovOperators

open MDPFinance.Bellman (Hist histState)

namespace BorelRobustMDP

universe u v

/-- Theorem 3.10 (Bäuerle & Glauner, arXiv:2007.13103v1, p.10; proof p.11). Under Assumptions 2.1 and
3.1:

a) `V_n(h_n) = J_n(x_n)` for all `h_n ∈ 𝓗_n`: deterministic Markov policies of both players suffice.
Moreover `J_n ∈ 𝔹`, `J_N = c_N` and `J_n = 𝒯_n J_{n+1}`. Markov minimizers `d*_n` of `J_{n+1}` exist, and
every sequence of them is an optimal policy of the controller.

b) If the ambiguity sets are weak* closed, then for every such `π* = (d*_0, …, d*_{N−1})` there are
maximizing decision rules `γ*_n` of nature with `J_n = 𝒯_{nd*_nγ*_n} J_{n+1}`, and every sequence
`γ* ∈ Γ^M` of rules with this equation satisfies `J_n = J_{nπ*γ*}`.

**Formalization Note.** Optimality of `π*` is `J_{nπ*} = J_n` and, with `π*` embedded in `Π^R` by Dirac
kernels, `V_{nπ*} = V_n` at feasible histories. In part b) the existence clause is for the stronger
class of rules, maximizing `L_n J_{n+1}(x, a, ·)` at every `(x, a) ∈ D_n`, and the clause "every
sequence" for the weaker class, the rules satisfying only `J_n = 𝒯_{nd*_nγ_n} J_{n+1}`. Part a) has no
closedness hypothesis. The printed `𝒯_{d*_nγ*_n}` is `𝒯_{nd*_nγ*_n}` of Definition 3.8. -/
theorem theorem_3_10 {E A : Type u} {Z : Type v} [TopologicalSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [StandardBorelSpace E]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A] [MeasurableSpace Z] {N : ℕ}
    (R : RobustModel E A Z N) (B : BoundingData E) (h21 : Assumption21 R.toDecisionModel)
    (h31 : Assumption31 R B) :
    (∀ n ≤ N, ∀ h : Hist E A n, R.Feasible n h →
      optimalValue R n h = markovOptimalValue R n (histState n h)) ∧
    (∀ n ≤ N, markovOptimalValue R n ∈ BB B.b) ∧
    (∀ x, markovOptimalValue R N x = R.cN x) ∧
    (∀ n < N, ∀ x,
      markovOptimalValue R n x = Tmin R n (markovOptimalValue R (n + 1)) x) ∧
    (∀ n < N, ∃ d : E → A, IsMinimizer R n (markovOptimalValue R (n + 1)) d) ∧
    (∀ d : MarkovPolicy R.toDecisionModel,
      (∀ n : Fin N, IsMinimizer R n (markovOptimalValue R (n + 1)) (d.rule n)) →
      (∀ n ≤ N, ∀ x, markovRobustValue R d n x = markovOptimalValue R n x) ∧
      ∀ n ≤ N, ∀ h : Hist E A n, R.Feasible n h →
        robustValue R d.toPolicy n h = optimalValue R n h) ∧
    ((∀ n, 1 ≤ n → n ≤ N → R.WeakStarClosed n) →
      ∀ d : MarkovPolicy R.toDecisionModel,
        (∀ n : Fin N, IsMinimizer R n (markovOptimalValue R (n + 1)) (d.rule n)) →
        (∀ n : Fin N, ∃ g : E × A → R.Amb (n + 1),
          IsMaximizer R n (markovOptimalValue R (n + 1)) g ∧
          ∀ x, markovOptimalValue R n x =
            Tdg R n (markovOptimalValue R (n + 1)) (d.rule n) g x) ∧
        ∀ γ : MarkovNature R,
          (∀ n : Fin N, ∀ x, markovOptimalValue R n x =
            Tdg R n (markovOptimalValue R (n + 1)) (d.rule n) (γ.rule n) x) →
          ∀ n ≤ N, ∀ x, markovOptimalValue R n x = markovValue R d γ n x) := by sorry

end BorelRobustMDP
