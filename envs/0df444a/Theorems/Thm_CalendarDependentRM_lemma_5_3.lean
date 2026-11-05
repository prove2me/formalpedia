-- Prove2me | Theorems.Thm_CalendarDependentRM_lemma_5_3
-- name    : CalendarDependentRM.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:37:31.030029+00:00
-- url     : https://prove2.me/theorems/54fbd06a-2f55-4339-9e1b-9c5ab9a5816f
-- title:
--   Lemma 5.3: availability probability bound
-- statement:
--   Assume the transition assumption with $\epsilon>0$, and let $x$ be feasible for the fluid approximation. With $U^0_i=0$, for all $k,i,t,q$ and $\lambda\in[0,1]$,
--
--   $$
--   P\Big\{U^{k-1}_i+\sum_{s=1}^tN^k_{is}(q)\ge c_i\ \Big|\ D^{k-1}=q\Big\}\le e^{(c_i+\frac3{\epsilon^6}(k-1))\lambda^2-(1-\gamma)c_i\lambda}.
--   $$
--
--   Choosing $\gamma$ and $\lambda$ suitably makes the right side at most $1/c_{\min}$, which through (3) and (4) gives the second term of the guarantee.
--
--   Differences from the source:
--   - generalization: $x$ an optimal solution of problem (2) → any feasible $x$; reason: the argument uses only the constraints of (2); an optimal solution is feasible
--   - reading: $P\{D^{k+1}=p\mid D^k=q\}\ge\epsilon$ for all $p,q\in\mathcal T$, $k\in\mathcal K$ → the bound holds for the transitions between stages of the horizon, into stages $2,\dots,K$, with no condition on $D^1$ given $\hat D^0$; reason: at $k=K$ the printed condition names a nonexistent $D^{K+1}$; this literal reading is the weakest hypothesis, so the result covers every other reading
--   - generalization: the draws $A^k_{jt}$, $X^k_{jt}(q)$ are independent Bernoulli variables, independent of the demands → `PolicyRun` lets the $X^k_{jt}(q)$ of different $(j,q)$ in one period be correlated; reason: one previous demand is active per period, so the argument needs no more; every fully independent family is a run
--   - encoding: stages $1,\dots,K$, periods and demands $1,\dots,T$ → 0-based indices `Fin K`, `Fin T`; reason: relabelling; the stated bounds translate each exponent accordingly
--   - encoding: the survival rate $\theta^k_t(q)$ is the primitive of the demand process → the transition law `trans` is primitive and $\theta$ is derived from it; reason: equivalent data
--   - encoding: conditional probabilities given a null event are undefined → they read $0$ (a ratio with $0/0=0$), or the zero measure for `cond`; reason: this only concerns states the policy never reaches, and such states have zero objective coefficient
-- source:
--   Li, Rusmevichientong & Topaloglu, Revenue Management with Calendar-Aware and Dependent Demands, arXiv:2409.02637v2, Lemma 5.3, p.18

import Mathlib
import Definitions.Def_CalendarDependentRM_PolicyRun

open MeasureTheory ProbabilityTheory

namespace CalendarDependentRM

/-- **Lemma 5.3 (Availability Probability Bound).** Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, Lemma 5.3, p. 18:
with `U⁰_i = 0`, for all `k`, `i`, `t`, `q` and `λ ∈ [0, 1]`,
`P{U^{k-1}_i + Σ_{s=1}^t N^k_is(q) ≥ c_i | D^{k-1} = q} ≤ e^{(c_i + (3/ε⁶)(k−1))λ² − (1−γ)c_iλ}`.

**Formalization Note** `k : Fin K` is the 0-based stage, so the paper's `k − 1` is `(k : ℕ)`. `T ε ≤ 1` is not assumed: for
the paper's `k ≥ 2`, `Minorized` implies it, and at the paper's `k = 1` the bound does not need it. `x` is feasible; the
paper's is optimal. -/
theorem lemma_5_3 {R J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    {K T : ℕ} {I : Instance R J K T} {ε : ℝ} (hε : 0 < ε) (hmin : I.chain.Minorized ε) {γ : ℝ}
    {x : Fin K → J → Fin T → Fin T → ℝ} (hx : I.Feasible x)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (run : PolicyRun I γ x P) (k : Fin K) (i : R) (t q : Fin T)
    {lamb : ℝ} (hl : lamb ∈ Set.Icc (0 : ℝ) 1) :
    (ProbabilityTheory.cond P {ω | run.Dprev k ω = q}).real (run.overBudget i k t q) ≤
      Real.exp (((I.c i : ℝ) + (3 / ε ^ 6) * ((k : ℕ) : ℝ)) * lamb ^ 2 -
        (1 - γ) * (I.c i : ℝ) * lamb) := by sorry

end CalendarDependentRM
