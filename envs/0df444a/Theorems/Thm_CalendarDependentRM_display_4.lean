-- Prove2me | Theorems.Thm_CalendarDependentRM_display_4
-- name    : CalendarDependentRM.display_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:37:20.109843+00:00
-- url     : https://prove2.me/theorems/cc5737fe-f567-4ace-85fa-dc7153139bad
-- title:
--   Display (4): availability from consumption tails
-- statement:
--   Fix $k,t,q$ and a product $j$ with resources $\mathcal L_j$, and suppose $P\{\Psi^k_t(q)=1\}>0$. Write $S_i=\sum_{\ell=1}^{k-1}\sum_s\sum_p\Psi^\ell_s(p)N^\ell_{is}(p)+\sum_{s=1}^tN^k_{is}(q)$ for the upper bound on the consumption of resource $i$. Then
--
--   $$
--   \begin{aligned}
--   P\{G^k_{jt}=1\mid\Psi^k_t(q)=1\}&\ge P\{S_i<c_i\ \forall i\in\mathcal L_j\mid\Psi^k_t(q)=1\}\\
--   &=1-P\{S_i\ge c_i\text{ for some }i\in\mathcal L_j\mid\Psi^k_t(q)=1\}\\
--   &\ge1-\sum_{i\in\mathcal L_j}P\{S_i\ge c_i\mid\Psi^k_t(q)=1\}\\
--   &=1-\sum_{i\in\mathcal L_j}P\{S_i\ge c_i\mid D^{k-1}=q\}.
--   \end{aligned}
--   $$
--
--   So it suffices to bound the tail of each $S_i$ given the demand of the previous stage.
--
--   Differences from the source:
--   - encoding: the conditional on $\Psi^k_t(q)=1$ is written without qualification → $0<P\{\Psi^k_t(q)=1\}$ is assumed; reason: the source's conditional is undefined otherwise, and the zero measure of `cond` would make the lower bounds false
--   - generalization: the draws $A^k_{jt}$, $X^k_{jt}(q)$ are independent Bernoulli variables, independent of the demands → `PolicyRun` lets the $X^k_{jt}(q)$ of different $(j,q)$ in one period be correlated; reason: one previous demand is active per period, so the argument needs no more; every fully independent family is a run
--   - encoding: stages $1,\dots,K$, periods and demands $1,\dots,T$ → 0-based indices `Fin K`, `Fin T`; reason: relabelling; the stated bounds translate each exponent accordingly
--   - encoding: the survival rate $\theta^k_t(q)$ is the primitive of the demand process → the transition law `trans` is primitive and $\theta$ is derived from it; reason: equivalent data
--   - generalization: $\bar x$ an optimal solution of problem (2) → any $x$ (no hypothesis on $x$); reason: each step of (4) is pathwise, the union bound, or the Markov property of the demands; an optimal solution is an instance
--   - generalization: the standing transition assumption $P\{D^{k+1}=p\mid D^k=q\}\ge\epsilon$ of §2, p.7 → no assumption on the transition law of the demands; reason: the last equality uses only the Markov property and the independence of the draws from the demands; every instance of the source is covered
-- source:
--   Li, Rusmevichientong & Topaloglu, Revenue Management with Calendar-Aware and Dependent Demands, arXiv:2409.02637v2, display (4), p.16

import Mathlib
import Definitions.Def_CalendarDependentRM_PolicyRun

open MeasureTheory ProbabilityTheory

namespace CalendarDependentRM

/-- **Display (4).** Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, display (4), p. 16, with its four steps:
`P{G^k_jt = 1 | Ψ^k_t(q) = 1} ≥ P{Σ_{ℓ<k} Σ_s Σ_p Ψ^ℓ_s(p) N^ℓ_is(p) + Σ_{s≤t} N^k_is(q) < c_i ∀ i ∈ 𝓛_j | Ψ^k_t(q) = 1}`
`= 1 − P{… ≥ c_i for some i ∈ 𝓛_j | Ψ^k_t(q) = 1}`
`≥ 1 − Σ_{i∈𝓛_j} P{… ≥ c_i | Ψ^k_t(q) = 1}`
`= 1 − Σ_{i∈𝓛_j} P{… ≥ c_i | D^{k-1} = q}`.

**Formalization Note** `0 < P{Ψ^k_t(q) = 1}` is assumed: the paper's conditional is undefined otherwise, and `P[|E]` on a
null `E` is the zero measure, on which the lower bounds would fail. `run.U i k` at the 0-based stage `k` is the paper's
triple sum over the earlier stages; `run.overBudget i k t q` is the event `{… ≥ c_i}`, and `I.A j` is `𝓛_j`. -/
theorem display_4 {R J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    {K T : ℕ} {I : Instance R J K T} {γ : ℝ} {x : Fin K → J → Fin T → Fin T → ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (run : PolicyRun I γ x P) (k : Fin K) (t q : Fin T) (j : J)
    (hpos : 0 < I.chain.prob (I.chain.reach k t q)) :
    (ProbabilityTheory.cond P (run.Psi k t q)).real
        {ω | ∀ i ∈ I.A j, run.U i (k : ℕ) ω + ∑ s ∈ Finset.Iic t, run.N i k s q ω < (I.c i : ℝ)} ≤
      (ProbabilityTheory.cond P (run.Psi k t q)).real {ω | run.G k t j ω} ∧
    (ProbabilityTheory.cond P (run.Psi k t q)).real
        {ω | ∀ i ∈ I.A j, run.U i (k : ℕ) ω + ∑ s ∈ Finset.Iic t, run.N i k s q ω < (I.c i : ℝ)} =
      1 - (ProbabilityTheory.cond P (run.Psi k t q)).real
        {ω | ∃ i ∈ I.A j, ω ∈ run.overBudget i k t q} ∧
    1 - ∑ i ∈ I.A j, (ProbabilityTheory.cond P (run.Psi k t q)).real (run.overBudget i k t q) ≤
      1 - (ProbabilityTheory.cond P (run.Psi k t q)).real
        {ω | ∃ i ∈ I.A j, ω ∈ run.overBudget i k t q} ∧
    1 - ∑ i ∈ I.A j, (ProbabilityTheory.cond P (run.Psi k t q)).real (run.overBudget i k t q) =
      1 - ∑ i ∈ I.A j,
        (ProbabilityTheory.cond P {ω | run.Dprev k ω = q}).real (run.overBudget i k t q) := by sorry

end CalendarDependentRM
