-- Prove2me | Theorems.Thm_BulowKlemperer429_Bundling_Supplement_lemma_5_4
-- name    : BulowKlemperer429.Bundling.Supplement.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:41:42.959194+00:00
-- url     : https://prove2.me/theorems/f6be4eea-fe61-4e34-8af9-7c414ed98d60
-- title:
--   Lemma 5.4 — revenue bounds for the improved seed and its intensity
-- statement:
--   Let $X$ be $0$ with probability $3/4$ and otherwise exponential with rate $1$, let $Y$ be $0$ with probability $1/12$ and otherwise exponential with rate $4$, independent, and $S_{\mathrm{seed}}=X+Y$. Let $c=1/4$, let $\mathrm{REV}_{\mathrm{seed}}=\tfrac12\Pr[S_{\mathrm{seed}}\ge\tfrac12]$ be the revenue of the seed bundle at price $1/2$, and let
--   $$\nu(x)=\frac{e^{-x}-e^{-4x/3}+e^{-4x}-e^{-48x}}{x}\qquad(x>0)$$
--   be the compound-Poisson intensity. Then
--   $$\mathrm{REV}(c+S_{\mathrm{seed}})=c=\tfrac14,\qquad\mathrm{REV}_{\mathrm{seed}}>\tfrac7{50},$$
--   and for every $t>0$,
--   $$t\int_t^\infty\nu(x)\,dx\le\frac9{80}.$$
--
--   These estimates feed the completion construction of Theorem 5.5: the gain $7/50-9/80=11/400$ relative to $c=1/4$ is the improvement $0.11$ beyond two.
--
--   **Formalization Note** The laws of $X$ and $Y$ are mixtures of a point mass at $0$ and Mathlib's exponential law, transported to $[0,\infty)$; $S_{\mathrm{seed}}$ has the convolution law. $\mathrm{REV}(c+S_{\mathrm{seed}})$ is the posted-price revenue of the shifted law. The integral of the nonnegative intensity is taken in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: X zero w.p. 3/4 else Exp(1); Y zero w.p. 1/12 else Exp(4); S_seed = X + Y independent → improvedSeedX, improvedSeedY: mixtures of dirac 0 and ProbabilityTheory.expMeasure (rate parametrization) pushed to ℝ≥0 by Real.toNNReal; improvedSeedLaw: their product pushed forward by addition; reason: the exponential law is supported on [0,∞), so the transport to ℝ≥0 changes nothing
--   - encoding: REV_seed := (1/2) Q(1/2) and REV(c + S_seed) with c = 1/4 → (1/2) · Pr[S_seed ≥ 1/2] and postedRevenue of the law of 1/4 + S_seed; reason: the source defines REV_seed as the revenue of the seed at price 1/2 (p. 18)
--   - encoding: t ∫_t^∞ ν(x) dx ≤ 9/80 with a real integral → ENNReal.ofReal t · ∫⁻ x in (t,∞), ENNReal.ofReal(ν x) ≤ ENNReal.ofReal(9/80); reason: ν ≥ 0 on (0,∞) since e^{−x} ≥ e^{−4x/3} and e^{−4x} ≥ e^{−48x}; the integral converges for t > 0, so the extended value is the real one
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 19, Lemma 5.4; proof Appendix C pp. 23–25 (PDF pp. 24–26) (PDF p. 20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
import Definitions.Def_BulowKlemperer429_Bundling_Revenue
import Definitions.Def_BulowKlemperer429_Bundling_Supplement_Seeds
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling.Supplement

theorem lemma_5_4 :
    postedRevenue (improvedSeedLaw.map (fun s => 1 / 4 + s)) = 1 / 4 ∧
      ENNReal.ofReal (7 / 50) < (1 / 2 : ℝ≥0∞) * improvedSeedLaw {x | 1 / 2 ≤ x} ∧
      ∀ t : ℝ, 0 < t →
        ENNReal.ofReal t * ∫⁻ x in Set.Ioi t, ENNReal.ofReal (intensity x) ≤
          ENNReal.ofReal (9 / 80) := by sorry


end BulowKlemperer429.Bundling.Supplement
