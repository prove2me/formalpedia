-- Prove2me | Theorems.Thm_CalendarDependentRM_theorem_4_1
-- name    : CalendarDependentRM.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:37:36.873236+00:00
-- url     : https://prove2.me/theorems/c0118cea-e48e-43c8-be4a-c8dc81dc7965
-- title:
--   Theorem 4.1 (Performance Guarantee)
-- statement:
--   Consider the network revenue management model with $K$ stages and Markov demands, where $P\{D^{k+1}=p\mid D^k=q\}\ge\epsilon>0$. Let $c_{\min}=\min_ic_i$ be the smallest capacity and $L=\max_j\sum_ia_{ij}$ the maximum number of resources used by a product. Let $\mathrm{APX}$ be the total expected revenue of the approximate policy built from an optimal solution of the fluid approximation (2) with tuning parameter $\gamma$. Then the fluid approximation has an optimal solution, and there is a choice of $\gamma\in[0,1]$ such that
--
--   $$
--   \frac{\mathrm{APX}}{\mathrm{OPT}}\ge\frac{\mathrm{APX}}{\overline Z_{LP}}\ge\max\Big\{\frac1{4L},\ 1-4\frac{\sqrt{(c_{\min}+\frac1{\epsilon^6}(K-1))\log c_{\min}}}{c_{\min}}-\frac L{c_{\min}}\Big\}.
--   $$
--
--   The first term is a constant-factor guarantee when $L$ is bounded. The second tends to one when the number of stages and the capacities scale at the same rate, so the policy is asymptotically optimal and the fluid bound asymptotically tight in that regime.
--
--   Differences from the source:
--   - reading: $P\{D^{k+1}=p\mid D^k=q\}\ge\epsilon$ for all $p,q\in\mathcal T$, $k\in\mathcal K$ → the bound holds for the transitions between stages of the horizon, into stages $2,\dots,K$, with no condition on $D^1$ given $\hat D^0$; reason: at $k=K$ the printed condition names a nonexistent $D^{K+1}$; this literal reading is the weakest hypothesis, so the result covers every other reading
--   - generalization: there exists a choice of $\gamma$ → one $\gamma\in[0,1]$ serves every optimal $x$ and every realization of the policy; reason: the proof's $\gamma$ depends only on $c_{\min},K,\epsilon,L$; fixing $x$ recovers the printed statement
--   - generalization: the draws $A^k_{jt}$, $X^k_{jt}(q)$ are independent Bernoulli variables, independent of the demands → `PolicyRun` lets the $X^k_{jt}(q)$ of different $(j,q)$ in one period be correlated; reason: one previous demand is active per period, so the argument needs no more; every fully independent family is a run
--   - encoding: ratios with $\mathrm{OPT}$, $\overline Z_{LP}$ in the denominator → a product inequality, plus the ratios when $0<\mathrm{OPT}$; reason: a ratio is undefined at $\mathrm{OPT}=0$, and Lean would read it as $0$
--   - encoding: $\overline Z_{LP}$ is the optimal objective value of problem (2) → `objective x` at an optimal `x`, with the existence of an optimum as a clause; reason: avoids a junk value from `sSup`; the feasible set is compact and nonempty
--   - encoding: $c_{\min}$ and $L$ appear in denominators, with $c\in\mathbb Z_+^{|\mathcal L|}$ → $1\le c_i$ for all $i$ and $1\le L$ (and, in Theorem 4.1, a nonempty $\mathcal L$ for the minimum); reason: excludes only the undefined fractions at $c_{\min}=0$ and $L=0$ and the empty minimum
--   - encoding: stages $1,\dots,K$, periods and demands $1,\dots,T$ → 0-based indices `Fin K`, `Fin T`; reason: relabelling; the stated bounds translate each exponent accordingly
--   - encoding: the survival rate $\theta^k_t(q)$ is the primitive of the demand process → the transition law `trans` is primitive and $\theta$ is derived from it; reason: equivalent data
--   - encoding: conditional probabilities given a null event are undefined → they read $0$ (a ratio with $0/0=0$), or the zero measure for `cond`; reason: this only concerns states the policy never reaches, and such states have zero objective coefficient
-- source:
--   Li, Rusmevichientong & Topaloglu, Revenue Management with Calendar-Aware and Dependent Demands, arXiv:2409.02637v2, Theorem 4.1, p.12

import Mathlib
import Definitions.Def_CalendarDependentRM_PolicyRun

open MeasureTheory ProbabilityTheory

namespace CalendarDependentRM

/-- **Theorem 4.1 (Performance Guarantee).** Li, Rusmevichientong & Topaloglu, *Technical Note – Revenue Management with
Calendar-Aware and Dependent Demands: Asymptotically Tight Fluid Approximations*, arXiv:2409.02637v2, Theorem 4.1, p. 12:
using `APX` to denote the total expected revenue of the approximate policy, there exists a choice of the tuning
parameter `γ` such that
`APX/OPT ≥ APX/Z_LP ≥ max{ 1/(4L), 1 − 4 √((c_min + (1/ε⁶)(K − 1)) log c_min) / c_min − L/c_min }`.

Problem (2) has an optimal solution; there is one `γ ∈ [0, 1]` such that for every optimal `x` and every realization of
the approximate policy built from `γ` and `x`, `OPT ≤ Z_LP`, `max{…} Z_LP ≤ APX`, and, when `0 < OPT`, the chain of ratios.

**Formalization Note** `Z_LP = I.objective x`. The ratios are also given as a product because Lean's `x / 0 = 0` makes
them empty at `OPT = 0`. `1 ≤ c_i` and `1 ≤ L` exclude only the undefined fractions at `c_min = 0` and `L = 0`. `Minorized ε`
is the literal transition assumption, with no condition on `D¹` given `D̂⁰`. There is no sign hypothesis on `f`. The same `γ`
serves all optimal solutions and all runs, which is stronger than one `γ` per solution. -/
theorem theorem_4_1 {R J : Type*} [Fintype R] [Nonempty R] [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] {K T : ℕ} [NeZero K] (I : Instance R J K T)
    (hc : ∀ i, 1 ≤ I.c i) (hL : 1 ≤ I.L) {ε : ℝ} (hε : 0 < ε) (hmin : I.chain.Minorized ε) :
    (∃ x, I.IsOptimal x) ∧
      ∃ γ ∈ Set.Icc (0 : ℝ) 1, ∀ x, I.IsOptimal x →
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (run : PolicyRun I γ x P),
          I.OPT ≤ I.objective x ∧
          I.bound ε * I.objective x ≤ run.APX ∧
          (0 < I.OPT → I.bound ε ≤ run.APX / I.objective x ∧
            run.APX / I.objective x ≤ run.APX / I.OPT) := by sorry

end CalendarDependentRM
