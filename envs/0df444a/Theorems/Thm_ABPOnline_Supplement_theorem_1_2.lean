-- Prove2me | Theorems.Thm_ABPOnline_Supplement_theorem_1_2
-- name    : ABPOnline.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:36:08.101914+00:00
-- url     : https://prove2.me/theorems/4ff35226-bc23-43a9-997c-1da0e49921ba
-- title:
--   Theorem 1.2 — zero margin, $1.73639<E_\star(0)\le\frac{243}{125}$ and $\frac{250}{243\pi}\le\alpha_{\mathrm{on}}(0)<\frac{200000}{173639\pi}$
-- statement:
--   Let $E_\star(0)$ be the Brownian control value at zero margin and $\alpha_{\mathrm{on}}(0)$ the online threshold of the asymmetric binary perceptron at zero margin. Then
--   $$
--   1.73639<E_\star(0)\le\frac{243}{125}=1.944,
--   $$
--   and consequently
--   $$
--   \frac{250}{243\pi}=0.3274793\ldots\le\alpha_{\mathrm{on}}(0)<\frac{200000}{173639\pi}=0.3666340\ldots .
--   $$
--
--   Together with Theorem 1.1, this gives a deterministic online algorithm at every fixed density $\alpha<250/(243\pi)$ at zero margin.
--
--   **Formalization Note** $E_\star(0)$ and $\alpha_{\mathrm{on}}(0)$ are extended nonnegative reals, and the bounds are the exact rationals $173639/100000$, $243/125$ and the reals $250/(243\pi)$, $200000/(173639\pi)$.
--
--   Differences from the source:
--   - generalization: E⋆(0) defined from a standard Brownian motion B = (B_t)_{0≤t≤1} with its completed natural filtration → the statement holds for every process B with IsBrownianOn1 B P on every probability space, with E⋆ computed on that B; reason: E⋆ depends only on the law of B; the source's Brownian motion is one such process
--   - encoding: E⋆(0), α_on(0) real numbers; decimal bounds 1.73639, 1.944 → E⋆ and α_on in ℝ≥0∞, compared with ENNReal.ofReal of the exact rationals 173639/100000 and 243/125 and of 250/(243π), 200000/(173639π); reason: the same inequalities; the decimals are exactly these rationals
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Theorem 1.2, (3)–(4), p.2 (PDF p.3)

import Mathlib
import Definitions.Def_ABPOnline_IsBrownianOn1
import Definitions.Def_ABPOnline_Estar
import Definitions.Def_ABPOnline_alphaOn

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ABPOnline.Supplement

/-- **Theorem 1.2 (Zero margin)** (Jo–Lee, arXiv:2609.02124, printed p.2, PDF p.3).
`1.73639 < E⋆(0) ≤ 243/125 = 1.944` (3), and consequently
`250/(243π) ≤ α_on(0) < 200000/(173639π)` (4).

**Formalization Note** `E⋆(0)` is the published `ABPOnline.Estar` computed on an arbitrary
standard Brownian motion `B` on `[0,1]` (published `ABPOnline.IsBrownianOn1`) on an arbitrary
probability space; `α_on` is the published `ABPOnline.alphaOn`. Both are in `ℝ≥0∞` and are compared
with `ENNReal.ofReal` of the exact rational bounds (`1.73639 = 173639/100000`,
`1.944 = 243/125`); the decimals `0.3274793…`, `0.3666340…` are display only. -/
theorem theorem_1_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianOn1 B P) :
    (ENNReal.ofReal (173639 / 100000) < Estar P B 0 ∧ Estar P B 0 ≤ ENNReal.ofReal (243 / 125)) ∧
    (ENNReal.ofReal (250 / (243 * Real.pi)) ≤ alphaOn 0 ∧
      alphaOn 0 < ENNReal.ofReal (200000 / (173639 * Real.pi))) := by sorry

end ABPOnline.Supplement
