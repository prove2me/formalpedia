-- Prove2me | Theorems.Thm_BauerleRiederMDP_NoArbitrage_remark_4_1_3
-- name    : BauerleRiederMDP.NoArbitrage.remark_4_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:27:00.795755+00:00
-- url     : https://prove2.me/theorems/e2c7c4f1-66f9-4f14-ac9a-11c24ee0bfce
-- title:
--   Remark 4.1.3 — the optimal portfolio is unique in a non-redundant market
-- statement:
--   Consider the one-period market of §4.1 (interest rate $i$, relative risk $R$ with $\mathbb E\|R\|<\infty$) and a utility function $U$ with $\operatorname{dom}U=[0,\infty)$ or $(0,\infty)$. Suppose the market is **non-redundant**: $a\cdot R=0$ $\mathbb P$-a.s. implies $a=0$, i.e. no asset can be perfectly replicated by a linear combination of the others. Then for every $x\in\operatorname{dom}U$ the optimal solution of
--   $$
--   v(x)=\sup_{a\in D(x)}u(x,a)
--   $$
--   is unique: if $a,b\in D(x)$ both satisfy $u(x,a)=u(x,b)=v(x)$, then $a=b$.
--
--   Together with Theorem 4.1.1 this gives a unique optimal portfolio $f^*(x)$ under no arbitrage.
--
--   Differences from the source:
--   - encoding: the $N$-period market of §3.1 on $(\Omega,\mathcal F,(\mathcal F_n),\mathbb P)$ with $\mathbb R^d$, time $n=0,\dots,N$ and $x\cdot y=\sum_k x_ky_k$ → `FinancialMarket`: data indexed by $n\in\mathbb N$ and constrained only for the times the book uses, $\mathbb R^d$ as `Fin d → ℝ`, inner products as finite sums; reason: the values at unused times never enter a statement; same objects
--   - reading: deterministic initial prices $s^k_0$, adapted prices $S^k_n$, $\tilde R^k_{n+1}>0$ a.s. → in addition $s^k_0>0$ and each $\tilde R_n$ is $\mathcal F$-measurable; reason: p.61 calls $\tilde R_n$ random variables on $(\Omega,\mathcal F,\mathbb P)$ and says the stock price stays positive, so these are the book's own standing assumptions made explicit
--   - encoding: the one-period problem of §4.1 with $i$, $\tilde R$, $R$ for $i_1$, $\tilde R_1$, $R_1$ → the market of §3.1 with $N=1$, using `M.i 1` and `M.relRisk 1`; reason: p.76 obtains the one-period problem exactly this way ("we skip the time index")
--   - encoding: Assumption $\mathbb E\|R\|<\infty$ with $\|x\|=|x_1|+\dots+|x_d|$ → `Integrable (M.relRisk 1) P`; reason: all norms on $\mathbb R^d$ are equivalent
--   - encoding: $u(x,a)=\mathbb E\,U((1+i)(x+a\cdot R))\in[-\infty,\infty)$ and $v=\sup_{a\in D(x)}u(x,a)$ → `expectedUtility` as $\int U^+\,d\mathbb P-\int U^-\,d\mathbb P$ in `EReal`, `valueFunction` as the `EReal` supremum; reason: values $-\infty$ and $+\infty$ stay representable; the positive part is finite under $\mathbb E\|R\|<\infty$ (p.76), so no $\infty-\infty$ occurs
--   - encoding: a utility function $U:\operatorname{dom}U\to\mathbb R$, right-continuous in $0$ when $\operatorname{dom}U=[0,\infty)$ → `U : ℝ → ℝ` with `IsUtilityFunction dom U` (strictly increasing, strictly concave, continuous on `dom`); reason: only the values on $\operatorname{dom}U$ are used; continuity on $[0,\infty)$ includes right-continuity in $0$
--   - generalization: uniqueness of the optimal solution of Theorem 4.1.1, which exists under no arbitrage → uniqueness of maximizers without the no-arbitrage hypothesis; reason: with an arbitrage there is no maximizer (Theorem 4.1.1 a)), so under no arbitrage the statement is the book's
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Remark 4.1.3, p.79 (PDF 93); non-redundancy, proof of Theorem 4.1.1, p.78 (PDF 92)

import Mathlib
import Definitions.Def_BauerleRiederMDP_NoArbitrage_IsUtilityFunction
import Definitions.Def_BauerleRiederMDP_NoArbitrage_valueFunction

open MeasureTheory

namespace BauerleRiederMDP.NoArbitrage

/-- Remark 4.1.3 (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance
(2011), Remark 4.1.3, p.79, PDF 93, with the definition of non-redundancy in the proof of
Theorem 4.1.1, p.78, PDF 92): the optimal solution of the one-period utility maximization problem
(4.2) is unique if the financial market is non-redundant, i.e. `a · R = 0` `ℙ`-a.s. necessarily
implies `a = 0`.

Setting of §4.1 (pp.76–77): the one-period market (`N = 1`, `i = i_1`, `R = R_1`), a utility
function `U` with `dom U = [0, ∞)` or `dom U = (0, ∞)`, and the standing assumption
`𝔼‖R‖ < ∞`. For every `x ∈ dom U`, any two maximizers `a, b ∈ D(x)` of `u(x, ·)` coincide.

**Formalization Note** `𝔼‖R‖ < ∞` is `Integrable R ℙ` (all norms on `ℝ^d` are equivalent). The
remark speaks of the optimal solution of Theorem 4.1.1, which exists under no arbitrage; the
uniqueness is stated here without that hypothesis (with an arbitrage there is no maximizer). -/
theorem remark_4_1_3 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (M : FinancialMarket Ω P d) (hN : M.N = 1)
    (dom : Set ℝ) (hdom : dom = Set.Ici 0 ∨ dom = Set.Ioi 0)
    (U : ℝ → ℝ) (hU : IsUtilityFunction dom U)
    (hR : Integrable (M.relRisk 1) P)
    (hnr : ∀ a : Fin d → ℝ, (∀ᵐ ω ∂P, ∑ k, a k * M.relRisk 1 ω k = 0) → a = 0) :
    ∀ x ∈ dom, ∀ a ∈ admissibleSet M dom x, ∀ b ∈ admissibleSet M dom x,
      expectedUtility M U x a = valueFunction M dom U x →
        expectedUtility M U x b = valueFunction M dom U x → a = b := by sorry

end BauerleRiederMDP.NoArbitrage
