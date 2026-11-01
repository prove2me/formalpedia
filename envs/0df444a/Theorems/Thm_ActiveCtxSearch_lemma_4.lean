-- Prove2me | Theorems.Thm_ActiveCtxSearch_lemma_4
-- name    : ActiveCtxSearch.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:41:42.775656+00:00
-- url     : https://prove2.me/theorems/d36e2428-14be-4e95-9ab7-8ff70b9a27c1
-- title:
--   Lemma 4 (corrected: scaling and cap) — $\wp$ separates from $1/2$ linearly in $|\hat b-b^*|$
-- statement:
--   Let $d\ge2$ and let an instance satisfy (A1)–(A3). Write $\wp(b)=\Pr_{x,\xi}[v(x)+\xi\ge b]$ for the label probability, $b^*$ for its $1/2$-point, and
--   $$s_0=2-|b^*+\mu^*|-\frac{\|w^*\|_2}{\sqrt{2(d-1)}}.$$
--   For every action $\hat b$,
--   $$\big|\wp(\hat b)-\tfrac12\big|\le\frac{C_\xi\,|\hat b-b^*|}{\|w^*\|_2}
--   \qquad\text{and}\qquad
--   \frac{0.07\,c_xc_\xi\min\{|\hat b-b^*|,\,s_0\}}{\|w^*\|_2}\le\big|\wp(\hat b)-\tfrac12\big|.$$
--
--   The two-sided comparison is what lets the confidence intervals of the trisection search decide on which side of $b^*$ each trisection point lies; it controls the number of queries in Lemma 2. When $s_0\le0$ the lower bound is vacuous.
--
--   Differences from the source:
--   - correction: |℘(b̂) − 1/2| ≤ C_ξ|b̂ − b*| → |℘(b̂) − 1/2| ≤ C_ξ|b̂ − b*|/‖w*‖₂; reason: the printed bound is false: d = 2, P_X = P_U, w* = (1/2, 0), μ* = 0, ξ ∼ Unif[−2, 2], c_ξ = C_ξ = 1/8 give b* = 0 and |℘(0.1) − 1/2| = 0.025 > C_ξ·0.1 = 0.0125
--   - correction: 0.07c_xc_ξ|b̂ − b*| ≤ |℘(b̂) − 1/2| → 0.07c_xc_ξ min{|b̂ − b*|, s₀}/‖w*‖₂ ≤ |℘(b̂) − 1/2|; reason: the printed bound is false for large gaps: the same instance with B = 100 and b̂ = 60 gives |℘ − 1/2| = 1/2 < 0.525; steps (8)–(11) keep both arguments of φ in [−2, 2] on the slab −r ≤ ⟨x, w*/‖w*‖⟩ ≤ 0, r = 1/√(2(d−1)), exactly when |b̂ − b*| ≤ s₀, and with the corrected Lemma 7 the slab constant is ≥ 0.087 ≥ 0.07
--   - reading: ℘(b) = Pr_x[v(x) ≥ b] and b* with Pr_x[v(x) ≥ b*] = 1/2 (pp.10–12, 17–18) → ℘(b) = Pr_{x,ξ}[v(x) + ξ ≥ b] and b* its 1/2-point; reason: Figure 2 (p.11), the proofs of Lemmas 1 and 4 and the quantity Algorithm 2 estimates all use the label probability
--   - reading: Lemma 4 states no condition on d → d ≥ 2; reason: Lemma 4 is stated inside the proof of Lemma 2, whose hypothesis d ≥ 2 it inherits; its proof uses r = 1/√(2(d−1))
--   - reading: ℘(b̂) = Pr_x[w(x) ≥ b̂] → ℘ in terms of v; reason: 'w(x)' is a typo for v(x)
-- source:
--   Chen, Liu & Wang, Active Learning for Contextual Search with Binary Feedback, arXiv:2110.01072v2, §4.1.2, Lemma 4, p.18

import Mathlib
import Definitions.Def_ActiveCtxSearch_Errors

open MeasureTheory

namespace ActiveCtxSearch

/-- **Lemma 4** (corrected: scaling by `1/‖w*‖₂` and a cap on the lower bound), Chen, Liu & Wang,
arXiv:2110.01072v2, p.18. Let `d ≥ 2` and an instance satisfy (A1)–(A3). For every action `b̂`,
`|℘(b̂) − 1/2| ≤ C_ξ |b̂ − b*| / ‖w*‖₂` and
`0.07 c_x c_ξ min{|b̂ − b*|, s₀} / ‖w*‖₂ ≤ |℘(b̂) − 1/2|`, where
`s₀ = 2 − |b* + μ*| − ‖w*‖₂ / √(2(d − 1))`.

**Formalization Note** `℘` and `b*` are the label probability and the label-balancing action. The
printed bounds `0.07 c_x c_ξ |b̂ − b*| ≤ |℘(b̂) − 1/2| ≤ C_ξ |b̂ − b*|` fail: the upper one at `d = 2`,
`w* = (1/2, 0)`, `ξ ∼ Unif[−2, 2]`, `c_ξ = C_ξ = 1/8`, `b̂ = 0.1`; the lower one with `B = 100`, `b̂ = 60`
(`℘ = 0`). `s₀` is the range on which steps (8)–(11) keep both arguments of `φ` in `[−2, 2]` on the slab
`−r ≤ ⟨x, w*/‖w*‖⟩ ≤ 0`, `r = 1/√(2(d−1))`; when `s₀ ≤ 0` the lower bound is vacuous. The hypothesis
`d ≥ 2` is that of Lemma 2, inside whose proof Lemma 4 is stated. -/
theorem lemma_4 (θ : Params) {d : ℕ} (hd : 2 ≤ d) (I : Problem d) (hA : Assumptions θ I)
    (b : ℝ) :
    |I.labelProb b - 1 / 2| ≤ θ.Cξ * |b - I.bStar| / ‖I.w‖ ∧
      0.07 * θ.cx * θ.cξ *
            min |b - I.bStar| (2 - |I.bStar + I.μ| - ‖I.w‖ / Real.sqrt (2 * ((d : ℝ) - 1))) /
          ‖I.w‖ ≤
        |I.labelProb b - 1 / 2| := by sorry

end ActiveCtxSearch
