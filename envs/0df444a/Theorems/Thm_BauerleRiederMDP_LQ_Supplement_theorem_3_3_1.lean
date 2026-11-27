-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_3_3_1
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_3_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T23:50:47.185553+00:00
-- url     : https://prove2.me/theorems/eac578e0-fe35-473f-8c1e-3cac4813f321
-- title:
--   Theorem 3.3.1 — the scaled binomial price processes converge weakly in D[0,T] to the Black–Scholes–Merton price
-- statement:
--   Let $\mu  \in  \mathbb R $, $\sigma  > 0$, $S_0 > 0$, $T > 0$, and for $N \in  \mathbb N $ let $u_N = 1 + \sigma /\sqrt N$, $d_N = 1 - \sigma /\sqrt N$, $p_N = 1/2 + \mu /(2\sigma \sqrt N)$. Let $(\tilde{R}^N_k)_k$ be independent and identically distributed, $u_N$ with probability $p_N$ and $d_N$ with probability $1 - p_N$, and $S^{(N)}_t := S_0 \prod _{k=1}^{\lfloor Nt\rfloor } \tilde{R}^N_k$, $t \in  [0, T]$. Then the sequence of stochastic processes $(S^{(N)}_t)$ converges weakly to the stock price $(S_t)$ in the Black–Scholes–Merton model, $dS_t = S_t(\mu  dt + \sigma  dW_t)$, i.e. $S_t = S_0 \exp ((\mu  - \sigma ^2/2) t + \sigma  W_t)$ for a Wiener process $W$, for $N \to  \infty $.
--
--   **Formalization Note.** Weak convergence is that of the laws on $D[0, T]$ with the Skorohod $J_1$ topology (Definition B.1.2), in the equivalent coupling form `ConvergesWeaklyInD` (the limit has continuous paths). The parameters are admissible ($0 < p_N < 1$) only for large $N$; the binomial variables are assumed i.i.d. with the stated law for every such $N$, and the convergence concerns large $N$ only. The Wiener process is Mathlib's `IsBrownianReal` (Brownian finite-dimensional laws, a.s. continuous paths), indexed by $\mathbb R \ge 0$; the price is the solution of the SDE written in closed form. The step is $h = 1/N$ with $\lfloor Nt\rfloor $ factors (empty product $1$ for $t < 1/N$).
--
--   Differences from the source:
--   - encoding: weak convergence of the laws on D[0,T] with the Skorohod topology → the coupling form ConvergesWeaklyInD (limit with continuous paths); reason: equivalent characterization of weak convergence to a continuous limit (Skorohod representation); same statement
--   - reading: for every N → for every N large enough that 0 < p_N < 1; reason: p_N is a probability only for large N; the convergence concerns N → ∞ only
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 3.3.1, p.70 (PDF 84)

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_ConvergesWeaklyInD

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem 3.3.1** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), Theorem 3.3.1, p.70, PDF 84, with the construction of §3.3, p.69, PDF 83). Let `μ ∈ ℝ`,
`σ > 0`, `S_0 > 0`, `T > 0`, and for `N ∈ ℕ` let
`u_N = 1 + σ/√N`, `d_N = 1 − σ/√N`, `p_N = 1/2 + μ/(2σ√N)`. Let `(R̃^N_k)_k` be independent and
identically distributed, `u_N` with probability `p_N` and `d_N` with probability `1 − p_N`, and
`S^{(N)}_t := S_0 ∏_{k=1}^{⌊Nt⌋} R̃^N_k`, `t ∈ [0, T]`. Then the sequence of stochastic processes
`(S^{(N)}_t)` converges weakly to the stock price `(S_t)` in the Black–Scholes–Merton model,
`dS_t = S_t(μ dt + σ dW_t)`, i.e. `S_t = S_0 exp((μ − σ²/2) t + σ W_t)` for a Wiener process `W`,
for `N → ∞`.

**Formalization Note.** Weak convergence is that of the laws on `D[0, T]` with the Skorohod `J_1`
topology (Definition B.1.2), in the equivalent coupling form `ConvergesWeaklyInD` (the limit has
continuous paths). The parameters are admissible (`0 < p_N < 1`) only for large `N`; the binomial
variables are assumed i.i.d. with the stated law for every such `N`, and the convergence concerns
large `N` only. The Wiener process is Mathlib's `IsBrownianReal` (Brownian finite-dimensional laws,
a.s. continuous paths), indexed by `ℝ≥0`; the price is the solution of the SDE written in closed
form. The step is `h = 1/N` with `⌊Nt⌋` factors (empty product `1` for `t < 1/N`). -/
theorem theorem_3_3_1 (μ σ S₀ T : ℝ) (hσ : 0 < σ) (hS₀ : 0 < S₀) (hT : 0 < T)
    {Ω : Type*} [MeasurableSpace Ω] (P : ℕ → Measure Ω) (hP : ∀ N, IsProbabilityMeasure (P N))
    (R : ℕ → ℕ → Ω → ℝ)
    (hR : ∀ᶠ N : ℕ in atTop,
      iIndepFun (R N) (P N) ∧ ∀ k, (∀ ω, R N k ω = 1 + σ / Real.sqrt N ∨
          R N k ω = 1 - σ / Real.sqrt N) ∧
        (P N) {ω | R N k ω = 1 + σ / Real.sqrt N} =
          ENNReal.ofReal (1 / 2 + μ / (2 * σ * Real.sqrt N)))
    (hRmeas : ∀ᶠ N : ℕ in atTop, ∀ k, Measurable (R N k))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (W : ℝ≥0 → Ω' → ℝ) (hW : IsBrownianReal W P') :
    ConvergesWeaklyInD T P
      (fun N ω t => S₀ * ∏ k ∈ Finset.Icc 1 ⌊(N : ℝ) * t⌋₊, R N k ω)
      P' (fun ω t => S₀ * Real.exp ((μ - σ ^ 2 / 2) * t + σ * W t.toNNReal ω)) := by sorry

end BauerleRiederMDP.LQ.Supplement
