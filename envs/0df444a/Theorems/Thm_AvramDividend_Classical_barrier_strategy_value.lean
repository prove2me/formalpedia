-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_strategy_value
-- name    : AvramDividend.Classical.barrier_strategy_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:56:59.029129+00:00
-- url     : https://prove2.me/theorems/5eb63c8f-c2ca-45bb-8a39-04e9d0d6b849
-- title:
--   Proposition 1 — value of the barrier strategy: $v_{\pi_a}(x)=W^{(q)}(x)/W^{(q)\prime}(a)$
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumptions (no monotone paths, $\mathbf E[X_1]>-\infty$, condition (3.3)), let $q>0$ and let $W=W^{(q)}$ be its $q$-scale function. Let $a>0$ and $0\le x\le a$. Then the expected discounted dividends paid until ruin by the barrier strategy $\pi_a$ started from capital $x$ are
--   $$\mathbf E_x\Bigl[\int_0^{\sigma_a}e^{-qt}\,dL^a_t\Bigr]=\frac{W^{(q)}(x)}{W^{(q)\prime}(a)},$$
--   where $\sigma_a$ is the ruin time of the controlled process $U^a=x+X-L^a$.
--
--   This identity gives the barrier value functions (5.1) and is the starting point of the whole optimization over barrier levels.
--
--   **Formalization Note.** The paper's display (3.12) also contains a middle term $\mathbf E_{x-a}[\int_0^{\hat\tau_a}e^{-qt}\,dS_t]$ for the process reflected at its supremum; it is the proof's intermediate quantity and is omitted. The value is stated in $[0,\infty]$, so the identity also asserts finiteness.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 7, Proposition 1, eq. (3.12)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrier_strategy_value {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) = ENNReal.ofReal (W x / deriv W a) := by sorry

end AvramDividend.Classical
