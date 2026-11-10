-- Prove2me | Theorems.Thm_AdaptiveRefresh_Main_contractive_freedman
-- name    : AdaptiveRefresh.Main.contractive_freedman
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:02:16.23455+00:00
-- url     : https://prove2.me/theorems/49aaff36-3bc0-4dd8-8e65-5babdfe6bd7f
-- title:
--   Lemma 4.4 — contractive Freedman inequality
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a probability space with filtration $(\mathcal F_i)_{i=0}^N$, and let $d>0$. Start $E_0=V_0=0$ in $\mathbb R^{d\times d}$. The matrices $P_i,W_i$ are $\mathcal F_{i-1}$-measurable, $W_i$ is symmetric, and $P_iP_i^\top\preceq I_d$. Each $Z_i$ is $\mathcal F_i$-measurable and symmetric, with conditional mean zero, conditional matrix square bounded above by $W_i$, and Euclidean operator norm at most $R\ge0$. Define
--
--   $$E_i=P_iE_{i-1}P_i^\top+Z_i,\qquad V_i=P_iV_{i-1}P_i^\top+W_i.$$
--
--   For every threshold $\tau\ge0$ and variance bound $\sigma^2\ge0$,
--
--   $$\Pr\{\exists i\le N:\|E_i\|\ge\tau\ \land\ \|V_i\|\le\sigma^2\}\le2d(N+1)\exp\!\left(-\frac{\tau^2}{2\sigma^2+(2/3)R\tau}\right).$$
--
--   No independence, commutation, diagonal restriction, deterministic contraction or deterministic variance process is assumed. The bounded increments ensure that their entries and matrix squares are integrable, so their conditional expectations are genuine.
--
--   Differences from the source:
--   - encoding: a filtration and conditional matrix expectations in positive finite dimension → explicit probability space and entrywise conditional expectations for 1≤i≤N; almost-everywhere matrix hypotheses; reason: bounded measurable increments on a probability space ensure integrability, with no bound added on P or W beyond the printed contraction and conditional-square assumptions
--   - encoding: variance scale σ² → a nonnegative real parameter named variance; reason: this is the bound σ² itself, not its square root
--   - reading: the exponential expression at zero denominator → factor 1 when τ=0 and factor 0 when τ>0; reason: these give the trivial bound and the zero-variance limiting bound; literal real division by zero would misstate the limit
-- source:
--   Maximilian Probst Gutenberg, Yu-Cheng Yeh, Gernot Zöcklein, STOC 2027 submission #894 (October 2026), Lemma 4.4, printed pp. 9–10 (PDF pp. 10–11), citing [GKG+26, Theorem 3.5]. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/894.pdf

import Mathlib
import Definitions.Def_AdaptiveRefresh_Main_MatrixProcess

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace AdaptiveRefresh.Main

/-- Lemma 4.4, printed pp. 9–10 / PDF pp. 10–11. All contractions and predictable
variance bounds are allowed; in particular P and W need not be deterministic or commute. -/
theorem contractive_freedman {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d N : ℕ) (hd : 0 < d)
    (F : Filtration ℕ mΩ)
    (P W Z : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (R variance τ : ℝ) (hR : 0 ≤ R) (hv : 0 ≤ variance) (hτ : 0 ≤ τ)
    (hP : ∀ i, 1 ≤ i → i ≤ N → ∀ u v, Measurable[F (i - 1)] (fun ω => P i ω u v))
    (hW : ∀ i, 1 ≤ i → i ≤ N → ∀ u v, Measurable[F (i - 1)] (fun ω => W i ω u v))
    (hZ : ∀ i, 1 ≤ i → i ≤ N → ∀ u v, Measurable[F i] (fun ω => Z i ω u v))
    (hWs : ∀ i, 1 ≤ i → i ≤ N → ∀ᵐ ω ∂μ, (W i ω).IsSymm)
    (hZs : ∀ i, 1 ≤ i → i ≤ N → ∀ᵐ ω ∂μ, (Z i ω).IsSymm)
    (hPc : ∀ i, 1 ≤ i → i ≤ N → ∀ᵐ ω ∂μ,
      Loewner (P i ω * (P i ω).transpose) 1)
    (hmean : ∀ i, 1 ≤ i → i ≤ N → ∀ᵐ ω ∂μ,
      conditionalMatrix μ (F (i - 1)) (Z i) ω = 0)
    (hvariance : ∀ i, 1 ≤ i → i ≤ N → ∀ᵐ ω ∂μ,
      Loewner (conditionalMatrix μ (F (i - 1)) (fun ξ => Z i ξ * Z i ξ) ω) (W i ω))
    (hincrement : ∀ i, 1 ≤ i → i ≤ N → ∀ᵐ ω ∂μ, opNorm (Z i ω) ≤ R) :
    μ {ω | ∃ i ≤ N, τ ≤ opNorm (matrixProcess P Z i ω) ∧
      opNorm (matrixProcess P W i ω) ≤ variance} ≤
      ENNReal.ofReal (2 * d * (N + 1) * freedmanFactor R variance τ) := by sorry

end AdaptiveRefresh.Main
