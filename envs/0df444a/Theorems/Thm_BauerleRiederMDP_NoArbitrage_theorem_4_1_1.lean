-- Prove2me | Theorems.Thm_BauerleRiederMDP_NoArbitrage_theorem_4_1_1
-- name    : BauerleRiederMDP.NoArbitrage.theorem_4_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:29:01.499211+00:00
-- url     : https://prove2.me/theorems/d1eec661-3540-40ac-b5fc-4115d55964bd
-- title:
--   Theorem 4.1.1 — an optimal one-period portfolio exists iff there is no arbitrage (corrected: b) under no arbitrage)
-- statement:
--   Let $U$ be a utility function with $\operatorname{dom}U=[0,\infty)$ or $\operatorname{dom}U=(0,\infty)$, and consider the one-period market of §4.1 with interest rate $i$ and relative risk $R$, $\mathbb E\|R\|<\infty$. With $D(x)$, $u(x,a)$ and $v(x)=\sup_{a\in D(x)}u(x,a)$ as in (4.2):
--
--   1. There are no arbitrage opportunities if and only if there exists a measurable function $f^*:\operatorname{dom}U\to\mathbb R^d$ with $f^*(x)\in D(x)$ and
--   $$
--   u\bigl(x,f^*(x)\bigr)=v(x),\qquad x\in\operatorname{dom}U .
--   $$
--   2. If there are no arbitrage opportunities, then $v$ is real-valued on $\operatorname{dom}U$ and strictly increasing, strictly concave and continuous on $\operatorname{dom}U$.
--
--   Absence of arbitrage is thus exactly the condition under which the one-period utility maximization problem has an optimal solution for every initial wealth; the regularity of $v$ is what the multiperiod terminal-wealth problems of §4.2 propagate backwards.
--
--   Differences from the source:
--   - encoding: the $N$-period market of §3.1 on $(\Omega,\mathcal F,(\mathcal F_n),\mathbb P)$ with $\mathbb R^d$, time $n=0,\dots,N$ and $x\cdot y=\sum_k x_ky_k$ → `FinancialMarket`: data indexed by $n\in\mathbb N$ and constrained only for the times the book uses, $\mathbb R^d$ as `Fin d → ℝ`, inner products as finite sums; reason: the values at unused times never enter a statement; same objects
--   - reading: deterministic initial prices $s^k_0$, adapted prices $S^k_n$, $\tilde R^k_{n+1}>0$ a.s. → in addition $s^k_0>0$ and each $\tilde R_n$ is $\mathcal F$-measurable; reason: p.61 calls $\tilde R_n$ random variables on $(\Omega,\mathcal F,\mathbb P)$ and says the stock price stays positive, so these are the book's own standing assumptions made explicit
--   - encoding: the one-period problem of §4.1 with $i$, $\tilde R$, $R$ for $i_1$, $\tilde R_1$, $R_1$ → the market of §3.1 with $N=1$, using `M.i 1` and `M.relRisk 1`; reason: p.76 obtains the one-period problem exactly this way ("we skip the time index")
--   - encoding: Assumption $\mathbb E\|R\|<\infty$ with $\|x\|=|x_1|+\dots+|x_d|$ → `Integrable (M.relRisk 1) P`; reason: all norms on $\mathbb R^d$ are equivalent
--   - encoding: $u(x,a)=\mathbb E\,U((1+i)(x+a\cdot R))\in[-\infty,\infty)$ and $v=\sup_{a\in D(x)}u(x,a)$ → `expectedUtility` as $\int U^+\,d\mathbb P-\int U^-\,d\mathbb P$ in `EReal`, `valueFunction` as the `EReal` supremum; reason: values $-\infty$ and $+\infty$ stay representable; the positive part is finite under $\mathbb E\|R\|<\infty$ (p.76), so no $\infty-\infty$ occurs
--   - encoding: a utility function $U:\operatorname{dom}U\to\mathbb R$, right-continuous in $0$ when $\operatorname{dom}U=[0,\infty)$ → `U : ℝ → ℝ` with `IsUtilityFunction dom U` (strictly increasing, strictly concave, continuous on `dom`); reason: only the values on $\operatorname{dom}U$ are used; continuity on $[0,\infty)$ includes right-continuity in $0$
--   - encoding: a measurable $f^*:\operatorname{dom}U\to\mathbb R^d$ with $u(x,f^*(x))=v(x)$ → a measurable `f : dom → (Fin d → ℝ)` (subspace σ-algebra) with `f x ∈ admissibleSet` and `expectedUtility … (f x) = valueFunction …`; reason: $u(x,a)$ is defined only for $a\in D(x)$ (p.77), so $f^*(x)\in D(x)$ only excludes undefined cases; it is an optimal solution of (4.2)
--   - encoding: $v$ strictly increasing, strictly concave and continuous on $\operatorname{dom}U$ → a real function $w$ equal to $v$ on $\operatorname{dom}U$ with `StrictMonoOn`, `StrictConcaveOn`, `ContinuousOn` on `dom`; reason: under no arbitrage $u(x,0)\le v(x)<\infty$, so $v$ is a real function on $\operatorname{dom}U$ as the book treats it
--   - correction: b) for every utility function, with or without arbitrage → b) under the hypothesis that there are no arbitrage opportunities; reason: counterexample satisfying every assumption of §4.1: $\operatorname{dom}U=[0,\infty)$, $U(x)=\sqrt x$, $i=0$, one stock with $\tilde R\in\{1,u\}$, $u>1$, $0<\mathbb P(\tilde R=u)<1$; every $a\ge0$ lies in $D(x)$ and $u(x,a)\to\infty$, so $v\equiv+\infty$, which is neither strictly increasing nor strictly concave; the book's proof of b) uses the compactness obtained from no arbitrage in a)
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 4.1.1, p.77 (PDF 91); setting §4.1, pp.76–77 (PDF 90–91)

import Mathlib
import Definitions.Def_BauerleRiederMDP_NoArbitrage_FinancialMarket_ArbitrageFree
import Definitions.Def_BauerleRiederMDP_NoArbitrage_IsUtilityFunction
import Definitions.Def_BauerleRiederMDP_NoArbitrage_valueFunction

open MeasureTheory

namespace BauerleRiederMDP.NoArbitrage

/-- Theorem 4.1.1 (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance
(2011), Theorem 4.1.1, p.77, PDF 91), with part b) under no arbitrage (correction). Let `U` be a
utility function with `dom U = [0, ∞)` or `dom U = (0, ∞)`. In the one-period market of §4.1
(`N = 1`, `i = i_1`, `R = R_1`, standing assumption `𝔼‖R‖ < ∞`, p.76):
a) there are no arbitrage opportunities if and only if there exists a measurable function
`f* : dom U → ℝ^d` with `f*(x) ∈ D(x)` and `u(x, f*(x)) = v(x)` for all `x ∈ dom U`;
b) if there are no arbitrage opportunities, then `v` is real-valued on `dom U` and strictly
increasing, strictly concave and continuous on `dom U`.

**Formalization Note** `u` and `v` are `EReal`-valued (`expectedUtility`, `valueFunction`). In a)
`f*(x)` is required to be admissible, `f*(x) ∈ D(x)`: an optimal solution of (4.2) is a point of
`D(x)`. `dom U` carries the subspace σ-algebra of the Borel σ-algebra of `ℝ`. In b) the real
function `w` is `v` on `dom U`, so `v` takes no infinite value there. Part b) is printed without
the no-arbitrage hypothesis, but it is false then: for `dom U = [0, ∞)`, `U(x) = √x`, `i = 0` and a
binomial stock with `R̃ ∈ {1, u}`, `u > 1`, `0 < ℙ(R̃ = u) < 1`, every `a ≥ 0` lies in `D(x)` and
`u(x, a) → ∞`, so `v ≡ +∞`. The book's proof of b) uses the compactness obtained from no arbitrage
in a). `𝔼‖R‖ < ∞` is `Integrable R ℙ` (all norms on `ℝ^d` are equivalent). -/
theorem theorem_4_1_1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (M : FinancialMarket Ω P d) (hN : M.N = 1)
    (dom : Set ℝ) (hdom : dom = Set.Ici 0 ∨ dom = Set.Ioi 0)
    (U : ℝ → ℝ) (hU : IsUtilityFunction dom U)
    (hR : Integrable (M.relRisk 1) P) :
    (M.ArbitrageFree ↔
      ∃ f : dom → (Fin d → ℝ), Measurable f ∧
        ∀ x : dom, f x ∈ admissibleSet M dom x ∧
          expectedUtility M U x (f x) = valueFunction M dom U x) ∧
    (M.ArbitrageFree →
      ∃ w : ℝ → ℝ, (∀ x ∈ dom, valueFunction M dom U x = (w x : EReal)) ∧
        StrictMonoOn w dom ∧ StrictConcaveOn ℝ dom w ∧ ContinuousOn w dom) := by sorry

end BauerleRiederMDP.NoArbitrage
