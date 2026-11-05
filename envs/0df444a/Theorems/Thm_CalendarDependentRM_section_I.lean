-- Prove2me | Theorems.Thm_CalendarDependentRM_section_I
-- name    : CalendarDependentRM.section_I
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:37:21.632197+00:00
-- url     : https://prove2.me/theorems/547a71d9-30e7-4eeb-84dd-f92082829c7e
-- title:
--   §I: the first term of the guarantee, $\mathrm{APX}\ge\gamma(1-L\gamma)\overline Z_{LP}$
-- statement:
--   Let $x$ be an optimal solution of the fluid approximation, $\gamma\in[0,1]$ and $c_i\ge1$ for all $i$. By the Markov inequality and the capacity constraints of (2), for all $i,k,t,q$,
--
--   $$
--   P\Big\{\sum_{\ell=1}^{k-1}\sum_s\sum_p\Psi^\ell_s(p)N^\ell_{is}(p)+\sum_{s=1}^tN^k_{is}(q)\ge c_i\ \Big|\ D^{k-1}=q\Big\}\le\gamma.
--   $$
--
--   Consequently
--
--   $$
--   \mathrm{APX}\ge\gamma(1-L\gamma)\overline Z_{LP},
--   $$
--
--   and setting $\gamma=1/(2L)$ with Theorem 3.1 gives $\frac1{4L}\le\mathrm{APX}/\overline Z_{LP}\le\mathrm{APX}/\mathrm{OPT}$. This is the constant-factor part of Theorem 4.1.
--
--   Differences from the source:
--   - reading: $P\{D^{k+1}=p\mid D^k=q\}\ge\epsilon$ for all $p,q\in\mathcal T$, $k\in\mathcal K$ → the bound holds for the transitions between stages of the horizon, into stages $2,\dots,K$, with no condition on $D^1$ given $\hat D^0$; reason: at $k=K$ the printed condition names a nonexistent $D^{K+1}$; this literal reading is the weakest hypothesis, so the result covers every other reading
--   - encoding: ratios with $\mathrm{OPT}$, $\overline Z_{LP}$ in the denominator → a product inequality, plus the ratios when $0<\mathrm{OPT}$; reason: a ratio is undefined at $\mathrm{OPT}=0$, and Lean would read it as $0$
--   - encoding: $c_{\min}$ and $L$ appear in denominators, with $c\in\mathbb Z_+^{|\mathcal L|}$ → $1\le c_i$ for all $i$ and $1\le L$ (and, in Theorem 4.1, a nonempty $\mathcal L$ for the minimum); reason: excludes only the undefined fractions at $c_{\min}=0$ and $L=0$ and the empty minimum
--   - generalization: the draws $A^k_{jt}$, $X^k_{jt}(q)$ are independent Bernoulli variables, independent of the demands → `PolicyRun` lets the $X^k_{jt}(q)$ of different $(j,q)$ in one period be correlated; reason: one previous demand is active per period, so the argument needs no more; every fully independent family is a run
--   - reading: the printed $E\{N\}$ lacks $\gamma$ on ER p.19, the Markov display has "$\ge c_i$" inside $E\{\cdot\}$, and $P\{G=1\mid D^{k-1}=q\}$ conditions on $D^{k-1}$ alone → the tail bound $\le\gamma$ and the revenue bound as derived by the argument; reason: printed slips: the conclusion uses $E\{N^k_{it}(q)\}=\sum_ja_{ij}\gamma x^k_{jt}(q)$, the Markov inequality applied to the sum, and the availability given $\Psi$ from (3)–(4)
--   - encoding: stages $1,\dots,K$, periods and demands $1,\dots,T$ → 0-based indices `Fin K`, `Fin T`; reason: relabelling; the stated bounds translate each exponent accordingly
--   - encoding: the survival rate $\theta^k_t(q)$ is the primitive of the demand process → the transition law `trans` is primitive and $\theta$ is derived from it; reason: equivalent data
--   - encoding: conditional probabilities given a null event are undefined → they read $0$ (a ratio with $0/0=0$), or the zero measure for `cond`; reason: this only concerns states the policy never reaches, and such states have zero objective coefficient
-- source:
--   Li, Rusmevichientong & Topaloglu, Revenue Management with Calendar-Aware and Dependent Demands, arXiv:2409.02637v2, §I, ER pp.19–20 (PDF 41–42), unnumbered

import Mathlib
import Definitions.Def_CalendarDependentRM_PolicyRun

open MeasureTheory ProbabilityTheory

namespace CalendarDependentRM

/-- **The first term of the guarantee.** Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, §I, Extended Results
pp. 19–20 (PDF pp. 41–42), unnumbered: by the Markov inequality,
`P{Σ_{ℓ<k} Σ_s Σ_p Ψ^ℓ_s(p) N^ℓ_is(p) + Σ_{s≤t} N^k_is(q) ≥ c_i | D^{k-1} = q} ≤ γ`, which yields
`APX ≥ γ (1 − Lγ) Z_LP`; setting `γ = 1/(2L)`, `1/(4L) ≤ APX/Z_LP ≤ APX/OPT`.

**Formalization Note** `1 ≤ c_i` and `1 ≤ L` exclude only the undefined `1/c_i` and `1/(2L)`. The ratios are stated as a
product, plus the quotients when `0 < OPT`. `x` is an optimal solution of (2), as in the paper. -/
theorem section_I {R J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    {K T : ℕ} {I : Instance R J K T} (hc : ∀ i, 1 ≤ I.c i) {ε : ℝ} (hε : 0 < ε)
    (hmin : I.chain.Minorized ε) {γ : ℝ} {x : Fin K → J → Fin T → Fin T → ℝ} (hx : I.IsOptimal x)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (run : PolicyRun I γ x P) :
    (∀ i k t q, (ProbabilityTheory.cond P {ω | run.Dprev k ω = q}).real (run.overBudget i k t q) ≤ γ) ∧
    γ * (1 - I.L * γ) * I.objective x ≤ run.APX ∧
    (1 ≤ I.L → γ = 1 / (2 * I.L) →
      1 / (4 * I.L) * I.objective x ≤ run.APX ∧
      (0 < I.OPT → 1 / (4 * I.L) ≤ run.APX / I.objective x ∧
        run.APX / I.objective x ≤ run.APX / I.OPT)) := by sorry

end CalendarDependentRM
