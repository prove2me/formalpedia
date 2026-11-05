-- Prove2me | Theorems.Thm_CalendarDependentRM_display_3
-- name    : CalendarDependentRM.display_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:37:22.759079+00:00
-- url     : https://prove2.me/theorems/cfcb03eb-1f9d-44da-b5db-8cfee978fe10
-- title:
--   Display (3): the expected revenue of the approximate policy
-- statement:
--   Let $x$ be a feasible solution of the fluid approximation and consider a realization of the approximate policy with tuning parameter $\gamma$. Its total expected revenue is
--
--   $$
--   \mathrm{APX}=\sum_k\sum_t\sum_j\sum_qf_jP\{D^k\ge t,D^{k-1}=q\}\,P\{G^k_{jt}=1\mid\Psi^k_t(q)=1\}\,\gamma x^k_{jt}(q).
--   $$
--
--   A lower bound on the availability probability $P\{G^k_{jt}=1\mid\Psi^k_t(q)=1\}$ thus converts directly into a lower bound on $\mathrm{APX}$ relative to the fluid objective.
--
--   Differences from the source:
--   - generalization: $x$ an optimal solution of problem (2) → any feasible $x$; reason: the argument uses only the constraints of (2); an optimal solution is feasible
--   - generalization: the draws $A^k_{jt}$, $X^k_{jt}(q)$ are independent Bernoulli variables, independent of the demands → `PolicyRun` lets the $X^k_{jt}(q)$ of different $(j,q)$ in one period be correlated; reason: one previous demand is active per period, so the argument needs no more; every fully independent family is a run
--   - encoding: stages $1,\dots,K$, periods and demands $1,\dots,T$ → 0-based indices `Fin K`, `Fin T`; reason: relabelling; the stated bounds translate each exponent accordingly
--   - encoding: the survival rate $\theta^k_t(q)$ is the primitive of the demand process → the transition law `trans` is primitive and $\theta$ is derived from it; reason: equivalent data
--   - encoding: conditional probabilities given a null event are undefined → they read $0$ (a ratio with $0/0=0$), or the zero measure for `cond`; reason: this only concerns states the policy never reaches, and such states have zero objective coefficient
--   - generalization: the standing transition assumption $P\{D^{k+1}=p\mid D^k=q\}\ge\epsilon$ of §2, p.7 → no assumption on the transition law of the demands; reason: the decomposition uses only the independence of the draws from the demands and the earlier periods; every instance of the source is covered
-- source:
--   Li, Rusmevichientong & Topaloglu, Revenue Management with Calendar-Aware and Dependent Demands, arXiv:2409.02637v2, display (3), p.15

import Mathlib
import Definitions.Def_CalendarDependentRM_PolicyRun

open MeasureTheory ProbabilityTheory

namespace CalendarDependentRM

/-- **Display (3).** Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, display (3), p. 15:
`APX = Σ_k Σ_t Σ_j Σ_q f_j P{D^k ≥ t, D^{k-1} = q} P{G^k_jt = 1 | Ψ^k_t(q) = 1} γ x^k_jt(q)`.

**Formalization Note** On a null `{Ψ^k_t(q) = 1}`, `P[|E]` is the zero measure and the first probability is `0`, so
the summand is `0` as the expected sales are. The paper takes `x` optimal for (2); the identity uses only feasibility. -/
theorem display_3 {R J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    {K T : ℕ} {I : Instance R J K T} {γ : ℝ} {x : Fin K → J → Fin T → Fin T → ℝ} (hx : I.Feasible x)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (run : PolicyRun I γ x P) :
    run.APX = ∑ k, ∑ t, ∑ j, ∑ q,
      I.f j * I.chain.prob (I.chain.reach k t q) *
        (ProbabilityTheory.cond P (run.Psi k t q)).real {ω | run.G k t j ω} * (γ * x k j t q) := by sorry

end CalendarDependentRM
