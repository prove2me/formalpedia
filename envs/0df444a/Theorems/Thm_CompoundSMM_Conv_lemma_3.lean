-- Prove2me | Theorems.Thm_CompoundSMM_Conv_lemma_3
-- name    : CompoundSMM.Conv.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:22.52596+00:00
-- url     : https://prove2.me/theorems/889b4a50-d11f-4b70-b14f-993ccd6206bc
-- title:
--   Lemma 3, p. 10 — under the sample-size growth conditions, Σ(1 − (N_{ν−1}/N_ν)²)N_{ν−1}^{−1/2} < ∞ and Σ (N_ν − N_{ν−1})^{1/2}/N_ν < ∞
-- statement:
--   Let $N_0,N_1,N_2,\dots$ be natural numbers (sample sizes). Suppose there are a positive integer $\bar\nu$ and scalars $c_1>0$, $c_2>0$ and $c_3<\bar\nu$ such that
--
--   $$\max\{N_{\nu-1}+1,\ c_2\,\nu^{1+2c_1}\}\ \le\ N_\nu\ \le\ \frac{N_{\nu-1}}{1-c_3/\nu}\qquad\text{for all }\nu>\bar\nu.$$
--
--   Then
--
--   $$\sum_{\nu}\Big(1-\Big(\frac{N_{\nu-1}}{N_\nu}\Big)^2\Big)\frac1{N_{\nu-1}^{1/2}}<\infty\qquad\text{and}\qquad\sum_{\nu}\frac{N_\nu-N_{\nu-1}}{N_\nu}\cdot\frac1{(N_\nu-N_{\nu-1})^{1/2}}<\infty.$$
--
--   These are the summability conditions under which the bounds of Proposition 2(c) on the error terms $e_{\nu,1},e_{\nu,2},e_{\nu,3}$ add up to a finite total, as the Robbins–Siegmund lemma requires.
--
--   **Formalization Note.** The positivity of $c_1$ and $c_2$ is added: without it $N_\nu=\nu$ satisfies the printed hypotheses ($c_1=0$, $c_2=c_3=1$, $\bar\nu=2$) and the second series is the harmonic series. The paper's series start at $\nu=1$, where $N_0=0$ produces a zero denominator; in Lean a term with a zero denominator is $0$, so the summability statement is about the series from the first $\nu$ at which every term is defined, which is what the paper means. Only finitely many terms are affected.
-- source:
--   Liu, Cui & Pang, Solving nonsmooth and nonconvex compound stochastic programs with applications to risk measure minimization, arXiv:2004.14342v3, p. 10, Lemma 3 (with c₁ > 0, c₂ > 0 added; proof in the appendix, pp. 45–46)

import Mathlib
import Definitions.Def_CompoundSMM_Conv_Setting

namespace CompoundSMM.Conv

/-- Lemma 3, p. 10 (with `c₁ > 0`, `c₂ > 0`): under the sample-size conditions,
`Σ_ν (1 − (N_{ν−1}/N_ν)²) N_{ν−1}^{−1/2} < ∞` and
`Σ_ν ((N_ν − N_{ν−1})/N_ν) (N_ν − N_{ν−1})^{−1/2} < ∞`. Terms with a zero denominator are `0`
(Lean's `1/0 = 0`), so the series are read from the first `ν` at which they are defined. -/
theorem lemma_3 (N : ℕ → ℕ) (hN : SampleSizeCond N) :
    Summable (fun ν : ℕ => (1 - ((N (ν - 1) : ℝ) / N ν) ^ 2) * (1 / Real.sqrt (N (ν - 1)))) ∧
    Summable (fun ν : ℕ =>
      ((N ν : ℝ) - N (ν - 1)) / N ν * (1 / Real.sqrt ((N ν : ℝ) - N (ν - 1)))) := by sorry

end CompoundSMM.Conv
