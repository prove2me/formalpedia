-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_lt_top
-- name    : AvramDividend.Classical.cstar_lt_top
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:57:31.963591+00:00
-- url     : https://prove2.me/theorems/7bb43015-9fa7-4b7a-a64d-2ef5c3f26c73
-- title:
--   Lemma 2(i) — the barrier level $c^*$ is finite
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumptions, let $q>0$ and let $W=W^{(q)}$ be its $q$-scale function. Then the barrier level
--   $$c^*=\inf\{a>0:\ W^{(q)\prime}(a)\le W^{(q)\prime}(x)\ \text{for all }x>0\}$$
--   (read as $0$ when this set is empty and $W^{(q)\prime}(0+)\le W^{(q)\prime}(x)$ for all $x>0$)
--   (with $W^{(q)\prime}(0)$ read as $W^{(q)\prime}(0+)$) is finite:
--   $$c^*<\infty.$$
--
--   Finiteness of $c^*$ means the candidate barrier strategy $\pi_{c^*}$ exists; it is used in Proposition 3, Lemma 3 and Theorem 2.
--
--   **Formalization Note.** $c^*$ takes values in $[0,\infty]$ with $\inf\emptyset=\infty$; see the definition item for the reading of (5.2) when the printed set is empty.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 15, Lemma 2(i)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem cstar_lt_top {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    cstar W < ⊤ := by sorry

end AvramDividend.Classical
