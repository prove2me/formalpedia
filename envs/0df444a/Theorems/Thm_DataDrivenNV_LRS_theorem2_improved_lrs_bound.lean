-- Prove2me | Theorems.Thm_DataDrivenNV_LRS_theorem2_improved_lrs_bound
-- name    : DataDrivenNV.LRS.theorem2_improved_lrs_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:25:57.487334+00:00
-- url     : https://prove2.me/theorems/78e30f3e-07be-4637-9827-b5c9761c0c7e
-- title:
--   Theorem 2, p. 9 — for 0 < ε ≤ 1, Q̂_N is ε-optimal with probability ≥ 1 − 2exp(−Nε²/(18+8ε) · min{b,h}/(b+h))
-- statement:
--   **Improved LRS bound.** Consider the newsvendor problem with underage cost $b>0$ and overage cost $h>0$ and a real-valued demand $D$ with law $\mu$ and $\mathbb E|D|<\infty$. Let $C(q)=\mathbb E[b(D-q)^+ + h(q-D)^+]$, let $q^*=\inf\{q:F(q)\ge b/(b+h)\}$ be the critical quantile, and let $\hat Q_N$ be the SAA solution, the $b/(b+h)$ quantile of an i.i.d. sample of size $N\ge1$ from $\mu$. Then for every $0<\epsilon\le1$, $\hat Q_N$ is $\epsilon$-optimal, i.e. $C(\hat Q_N)\le(1+\epsilon)C(q^*)$, with probability at least
--   $$1-2\exp\Big(-\frac{N\epsilon^2}{18+8\epsilon}\cdot\frac{\min\{b,h\}}{b+h}\Big).$$
--
--   The bound holds for every demand distribution. Compared with the bound of Levi, Roundy and Shmoys (2007), the exponent depends on $\min\{b,h\}/(b+h)$ rather than on its square, so the required sample size grows much more slowly when the critical ratio $b/(b+h)$ is close to $0$ or $1$.
--
--   **Formalization Note** The statement bounds the probability, under the product measure $\mu^{\otimes N}$, of the event that $\hat Q_N$ is not $\epsilon$-optimal. The paper states the theorem "for any $\epsilon>0$"; it is restricted here to $0<\epsilon\le1$, because it is false for large $\epsilon$. Counterexample: $b=h=1$, $N=1$, $D\in\{0,M\}$ with $\Pr(D=M)=0.005$. Then $q^*=0$, $C(0)=0.005M$, $\hat Q_1=D^1$ and $C(M)=0.995M$, so $\hat Q_1$ has relative regret $198$ with probability $0.005$, while at $\epsilon=150$ the bound promises a failure probability of about $2\exp(-22500/2436)\approx1.9\cdot10^{-4}$. The hypothesis $\mathbb E|D|<\infty$ makes $C$ a genuine expectation; without it the Lean integral is $0$ and the statement would be trivial.
-- source:
--   Levi, Perakis & Uichanco, The Data-Driven Newsvendor Problem: New Bounds and Insights, authors' accepted manuscript (MIT DSpace), p. 9, Theorem 2 and display (5); proof in EC.1, pp. ec5–ec6

import Mathlib
import Definitions.Def_DataDrivenNV_LRS_Setting

open MeasureTheory ProbabilityTheory

namespace DataDrivenNV.LRS

/-- Theorem 2 (Improved LRS bound), p. 9, display (5). For a demand law `μ` with `E|D| < ∞`, an
i.i.d. sample of size `N ≥ 1` and `0 < ε ≤ 1`, the SAA quantile `Q̂_N` fails to be `ε`-optimal
with probability at most `2 exp(-(Nε²/(18 + 8ε)) · min{b,h}/(b + h))`. The restriction `ε ≤ 1`
is needed: the printed statement "for any ε > 0" fails for large `ε`. -/
theorem theorem2_improved_lrs_bound (b h : ℝ) (hb : 0 < b) (hh : 0 < h)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (N : ℕ) (hN : 1 ≤ N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (Measure.pi fun _ : Fin N => μ)
        {x : Fin N → ℝ | ¬ IsEpsOptimal μ b h ε (saaQuantile b h x)} ≤
      ENNReal.ofReal
        (2 * Real.exp (-((N : ℝ) * ε ^ 2 / (18 + 8 * ε) * (min b h / (b + h))))) := by sorry

end DataDrivenNV.LRS
