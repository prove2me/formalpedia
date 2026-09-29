-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleDeriv_inf_attained
-- name    : AvramDividend.Classical.scaleDeriv_inf_attained
-- status  : Open
-- author  : @WillR
-- created : 2026-09-28T01:18:05.844988+00:00
-- url     : https://prove2.me/theorems/e489a83e-02e5-4094-a532-137d368a6d02
-- title:
--   The infimum of the scale-function derivative on $(0,\infty)$ is attained, or is the right limit $W^{(q)\prime}(0+)$
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumptions of Avram, Palmowski, Pistorius, let $q>0$, and let $W=W^{(q)}$ be its $q$-scale function. Then the derivative $W'$ has its infimum over $(0,\infty)$ either at an interior point $a>0$, or at the right endpoint $0$ in the sense that $W^{(q)\prime}(0+)$ already lies below every value $W'(x)$ for $x>0$.
--
--   This is the dichotomy that makes the barrier level (5.2), $c^*=\inf\{a>0: W'(a)\le W'(x)\ \forall x>0\}$, well defined and finite: whichever side of the dichotomy holds, the set in (5.2) is nonempty or the endpoint case $c^*=0$ applies, and in either case $c^*<\infty$.
--
--   The paper (Lemma 2(i), p. 15) obtains this from the fact that $W'$ is nonnegative and continuous for $y>0$ and increases to $\infty$ as $y\to\infty$: a continuous function on $(0,\infty)$ that tends to $+\infty$ attains its infimum if the infimum is not the limit at the left endpoint, and otherwise the left-endpoint value $W'(0+)$ is already minimal.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, Lemma 2(i) (p. 15), used in Proposition 3(i) (p. 15) and Theorem 2 (p. 16).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleDeriv_inf_attained {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    (∃ a : ℝ, 0 < a ∧ ∀ x : ℝ, 0 < x → deriv W a ≤ deriv W x) ∨
      ∀ x : ℝ, 0 < x → derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal) := by sorry

end AvramDividend.Classical
