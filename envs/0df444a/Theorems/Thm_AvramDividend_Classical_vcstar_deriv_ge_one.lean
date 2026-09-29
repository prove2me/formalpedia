-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one
-- name    : AvramDividend.Classical.vcstar_deriv_ge_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:58:42.686185+00:00
-- url     : https://prove2.me/theorems/d42fc3e4-7a32-428c-80a3-1827a721cf4f
-- title:
--   Lemma 3(i) — $v_{c^*}'(x)\ge1$ for $x>0$
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumptions, let $q>0$ and let $W=W^{(q)}$ be its $q$-scale function. Then the candidate value function $v_{c^*}$ is differentiable at every $x>0$ and
--   $$v_{c^*}'(x)\ge1\qquad(x>0).$$
--
--   This is the gradient half of the variational inequality (5.8), $\max\{\Gamma w-qw,\,1-w'\}=0$, for $w=v_{c^*}$: paying a marginal dividend is never better than keeping it.
--
--   **Formalization Note.** Differentiability is stated along with the bound, so that the bound is not satisfied by a default value of the derivative. The paper states the lemma under "Let $x,a>0$"; the parameter $a$ plays no role in part (i).
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 16, Lemma 3(i)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem vcstar_deriv_ge_one {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (vcstar W) x ∧ 1 ≤ deriv (vcstar W) x := by sorry

end AvramDividend.Classical
