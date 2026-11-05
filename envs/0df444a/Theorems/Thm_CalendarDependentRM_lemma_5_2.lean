-- Prove2me | Theorems.Thm_CalendarDependentRM_lemma_5_2
-- name    : CalendarDependentRM.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:37:41.482863+00:00
-- url     : https://prove2.me/theorems/0ed22be6-87b5-4e26-b7d9-647c871ffb96
-- title:
--   Lemma 5.2: moment generating function bound for the martingale
-- statement:
--   Assume the transition assumption with $\epsilon>0$, and let $x$ be feasible for the fluid approximation. With $M^0_i(0)=0$, for all $k$, $i$, $\ell=0,\dots,k-1$, $t,q$ and $\lambda\ge0$,
--
--   $$
--   E\Big\{e^{\lambda\big(M^{k-1}_i(\ell)+\sum_{s=1}^tn^k_{is}(q)\big)}\ \Big|\ D^{k-1}=q\Big\}\le e^{\frac2{\epsilon^6}(k-1-\ell)\lambda^2+\gamma c_i\lambda}.
--   $$
--
--   This is the core concentration estimate: the first term of the exponent comes from the martingale increments, and the second from the capacity constraint of the fluid approximation.
--
--   Differences from the source:
--   - encoding: $t,q$ are not bound by the printed quantifiers → for all $t,q$; reason: the proof and its use in Lemma 5.3 hold them arbitrary
--   - reading: $\ell=0,\dots,k-1$, with only $M^0_i(0)=0$ defined at $\ell=0$, while the proof runs over $\ell\ge1$ → $M^m_i(\ell)$ for all these $\ell$, conditioning on the demands of stages in $[\ell,m]$ with $\ell\ge1$ effective; reason: $D^0$ is deterministic, so $M^{k-1}_i(0)=M^{k-1}_i(1)$ for $k\ge2$; the bound at $\ell=0$ is then weaker than at $\ell=1$, and $M^0_i(0)=0$ as printed
--   - generalization: $x$ an optimal solution of problem (2) → any feasible $x$; reason: the argument uses only the constraints of (2); an optimal solution is feasible
--   - reading: $P\{D^{k+1}=p\mid D^k=q\}\ge\epsilon$ for all $p,q\in\mathcal T$, $k\in\mathcal K$ → the bound holds for the transitions between stages of the horizon, into stages $2,\dots,K$, with no condition on $D^1$ given $\hat D^0$; reason: at $k=K$ the printed condition names a nonexistent $D^{K+1}$; this literal reading is the weakest hypothesis, so the result covers every other reading
--   - encoding: stages $1,\dots,K$, periods and demands $1,\dots,T$ → 0-based indices `Fin K`, `Fin T`; reason: relabelling; the stated bounds translate each exponent accordingly
--   - encoding: the survival rate $\theta^k_t(q)$ is the primitive of the demand process → the transition law `trans` is primitive and $\theta$ is derived from it; reason: equivalent data
--   - encoding: conditional probabilities given a null event are undefined → they read $0$ (a ratio with $0/0=0$), or the zero measure for `cond`; reason: this only concerns states the policy never reaches, and such states have zero objective coefficient
--   - generalization: the draws $A^k_{jt}$, $X^k_{jt}(q)$ are independent Bernoulli variables, independent of the demands → `PolicyRun` lets the $X^k_{jt}(q)$ of different $(j,q)$ in one period be correlated; reason: the statement involves the run only through its demands and the deterministic $n^k_{it}(q)$; every fully independent family is a run
-- source:
--   Li, Rusmevichientong & Topaloglu, Revenue Management with Calendar-Aware and Dependent Demands, arXiv:2409.02637v2, Lemma 5.2, p.17

import Mathlib
import Definitions.Def_CalendarDependentRM_PolicyRun

open MeasureTheory ProbabilityTheory

namespace CalendarDependentRM

/-- **Lemma 5.2 (Moment Generating Function Bound).** Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, Lemma 5.2, p. 17:
with `M⁰_i(0) = 0`, for all `k`, `i`, `ℓ = 0, …, k − 1` and `λ ≥ 0`,
`E{e^{λ(M^{k-1}_i(ℓ) + Σ_{s=1}^t n^k_is(q))} | D^{k-1} = q} ≤ e^{(2/ε⁶)(k−1−ℓ)λ² + γ c_i λ}`.

**Formalization Note** `k : Fin K` is the 0-based stage, so the paper's `k − 1` is `(k : ℕ)`, and `ℓ ≤ k` is the paper's
range of `ℓ`. See `PolicyRun.M` for the meaning of the paper's `ℓ = 0`. The statement holds for all `t`, `q`, as in the
paper's use, and for feasible `x`. -/
theorem lemma_5_2 {R J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    {K T : ℕ} {I : Instance R J K T} {ε : ℝ} (hε : 0 < ε) (hmin : I.chain.Minorized ε) {γ : ℝ}
    {x : Fin K → J → Fin T → Fin T → ℝ} (hx : I.Feasible x)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (run : PolicyRun I γ x P) (k : Fin K) (i : R) (ℓ : ℕ) (hℓ : ℓ ≤ (k : ℕ)) (t q : Fin T)
    {lamb : ℝ} (hl : 0 ≤ lamb) :
    ∫ ω, Real.exp (lamb * (run.M i (k : ℕ) ℓ ω + ∑ s ∈ Finset.Iic t, I.meanN γ x i k s q))
        ∂(ProbabilityTheory.cond P {ω | run.Dprev k ω = q}) ≤
      Real.exp ((2 / ε ^ 6) * (((k : ℕ) : ℝ) - (ℓ : ℝ)) * lamb ^ 2 + γ * (I.c i : ℝ) * lamb) := by sorry

end CalendarDependentRM
