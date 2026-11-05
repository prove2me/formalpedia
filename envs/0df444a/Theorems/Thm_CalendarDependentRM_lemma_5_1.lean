-- Prove2me | Theorems.Thm_CalendarDependentRM_lemma_5_1
-- name    : CalendarDependentRM.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:37:26.662544+00:00
-- url     : https://prove2.me/theorems/f61a8b96-b4d3-430e-a213-7902ead4a55c
-- title:
--   Lemma 5.1 (corrected: $T\epsilon\le1$): moment generating function gap
-- statement:
--   Let $x$ be feasible for the fluid approximation, $\epsilon>0$ with $T\epsilon\le1$. For all stages $k$, resources $i$ and $\lambda\ge0$,
--
--   $$
--   E\{e^{\lambda U^k_i}\mid D^k\}\le e^{\frac1{2\epsilon}k\lambda^2}E\{e^{\lambda V^k_i}\mid D^k\}.
--   $$
--
--   So the moment generating function of the realized consumption $U^k_i$ is controlled by that of its demand-measurable proxy $V^k_i$, up to a factor that accounts for the randomness of the requests and acceptance draws.
--
--   Differences from the source:
--   - correction: no assumption beyond the standing transition assumption, from which the proof derives $T\le1/\epsilon$ → $T\epsilon\le1$ is assumed, in place of that assumption; reason: at $K=1$ the transition assumption is empty and the printed lemma is false: for $K=1$, $T=5$, $D^1\equiv5$, one resource and product with $a=1$, $\lambda=1$, $x=1/2$, $c=3$, $\gamma=1$, $\epsilon=1$, $\lambda_{\mathrm{mgf}}=1/2$, we get $E\,e^{\lambda(U-V)}=\cosh(1/4)^5\approx1.167>e^{1/8}\approx1.133$. $T\epsilon\le1$ holds whenever $K\ge2$
--   - generalization: $x$ an optimal solution of problem (2) → any feasible $x$; reason: the argument uses only the constraints of (2); an optimal solution is feasible
--   - generalization: the draws $A^k_{jt}$, $X^k_{jt}(q)$ are independent Bernoulli variables, independent of the demands → `PolicyRun` lets the $X^k_{jt}(q)$ of different $(j,q)$ in one period be correlated; reason: one previous demand is active per period, so the argument needs no more; every fully independent family is a run
--   - encoding: $E\{\cdot\mid D^k\}$ is a random variable → the inequality at each value $q$ of $D^k$, with the conditional measure; reason: equivalent on a finite space; at a null value both sides vanish
--   - encoding: stages $1,\dots,K$, periods and demands $1,\dots,T$ → 0-based indices `Fin K`, `Fin T`; reason: relabelling; the stated bounds translate each exponent accordingly
--   - encoding: the survival rate $\theta^k_t(q)$ is the primitive of the demand process → the transition law `trans` is primitive and $\theta$ is derived from it; reason: equivalent data
-- source:
--   Li, Rusmevichientong & Topaloglu, Revenue Management with Calendar-Aware and Dependent Demands, arXiv:2409.02637v2, Lemma 5.1, p.16

import Mathlib
import Definitions.Def_CalendarDependentRM_PolicyRun

open MeasureTheory ProbabilityTheory

namespace CalendarDependentRM

/-- **Lemma 5.1 (Moment Generating Function Gap)**, corrected. Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2,
Lemma 5.1, p. 16: for all `k`, `i` and `λ ≥ 0`, `E{e^{λU^k_i} | D^k} ≤ e^{(1/(2ε)) k λ²} E{e^{λV^k_i} | D^k}`.

**Formalization Note** `k : Fin K` is the 0-based stage, so the paper's `k` is `k + 1`, and `U^k_i = run.U i (k + 1)`. The
conditional expectation is stated at each value `q` of `D^k`; `P[|E]` on a null event is the zero measure and both sides
vanish. `T ε ≤ 1` is assumed instead of the transition assumption: the printed proof derives it from
`P{D^{k+1} = p | D^k = q} ≥ ε`, but at `K = 1` that assumption is empty, and the lemma fails without it
(`K = 1`, `T = 5`, `D¹ ≡ 5`, one resource and product, `λ_jt = 1`, `x = 1/2`, `γ = 1`, `ε = 1`, `λ = 1/2`:
`cosh(1/4)⁵ ≈ 1.167 > e^{1/8} ≈ 1.133`). -/
theorem lemma_5_1 {R J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    {K T : ℕ} {I : Instance R J K T} {ε : ℝ} (hε : 0 < ε) (hT : (T : ℝ) * ε ≤ 1) {γ : ℝ}
    {x : Fin K → J → Fin T → Fin T → ℝ} (hx : I.Feasible x)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (run : PolicyRun I γ x P) (k : Fin K) (i : R) (q : Fin T) {lamb : ℝ} (hl : 0 ≤ lamb) :
    ∫ ω, Real.exp (lamb * run.U i ((k : ℕ) + 1) ω) ∂(ProbabilityTheory.cond P {ω | run.D k ω = q}) ≤
      Real.exp ((1 / (2 * ε)) * (((k : ℕ) : ℝ) + 1) * lamb ^ 2) *
        ∫ ω, Real.exp (lamb * run.V i ((k : ℕ) + 1) ω) ∂(ProbabilityTheory.cond P {ω | run.D k ω = q}) := by sorry

end CalendarDependentRM
