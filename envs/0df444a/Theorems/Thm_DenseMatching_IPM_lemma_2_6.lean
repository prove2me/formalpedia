-- Prove2me | Theorems.Thm_DenseMatching_IPM_lemma_2_6
-- name    : DenseMatching.IPM.lemma_2_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:41:05.256561+00:00
-- url     : https://prove2.me/theorems/44c03e21-631f-49d2-8985-0db542275cf0
-- title:
--   Lemma 2.6 — ln E[e^{xζ}] ≤ 0.51x²/ϱ for the centered retention variable, |x| ≤ 10⁻³ϱ
-- statement:
--   Let $\zeta$ be the centered retention variable of intensity $\varrho>0$: with $p=1-e^{-\varrho}$, $\zeta=1/p-1$ with probability $p$ and $\zeta=-1$ otherwise. Then for every real $x$ with $|x|\le10^{-3}\varrho$,
--   $$\ln\mathbb E[e^{x\zeta}]\le\frac{0.51\,x^2}{\varrho}.\tag{1}$$
--   It is the scalar moment-generating-function estimate applied with Tropp's master tail bound (Lemma 2.4) in §5.
--
--   Differences from the source:
--   - reading: log E[e^{xζ}] under the convention 'All logarithms are base 2' (p. 7) → Real.log (natural logarithm); reason: the proof ends with 'log g(x) ≤ g(x) − 1', which holds for ln only; with log₂ the printed bound fails (ϱ = 10⁻³, x = 10⁻⁶ gives log₂ E[e^{xζ}] ≈ 0.72 x²/ϱ); recorded as typo insight I2
-- source:
--   Dai, Peng, Sleator, Stepin, Yang, Approaching Optimality for Dense Bipartite Matching, STOC 2027 submission (manuscript sha256 0bdeb447…), p. 9, Lemma 2.6

import Mathlib
import Definitions.Def_DenseMatching_IPM_Tools

namespace DenseMatching.IPM

/-- Lemma 2.6 (p. 9), with `log` read as the natural logarithm. Let `ζ` be the centered retention
variable of intensity `ϱ > 0` (`ζ = 1/p − 1` with probability `p = 1 − e^{−ϱ}`, `ζ = −1`
otherwise). Then for every real `x` with `|x| ≤ 10⁻³ϱ`, `ln E[e^{xζ}] ≤ 0.51 x²/ϱ`. -/
theorem lemma_2_6 (ϱ : ℝ) (hϱ : 0 < ϱ) (x : ℝ) (hx : |x| ≤ 1 / 10 ^ 3 * ϱ) :
    Real.log (∫ y, Real.exp (x * y) ∂(retentionLaw ϱ)) ≤ 0.51 * x ^ 2 / ϱ := by sorry

end DenseMatching.IPM
