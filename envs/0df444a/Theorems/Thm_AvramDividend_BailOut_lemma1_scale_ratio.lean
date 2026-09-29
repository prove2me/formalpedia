-- Prove2me | Theorems.Thm_AvramDividend_BailOut_lemma1_scale_ratio
-- name    : AvramDividend.BailOut.lemma1_scale_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:04:06.163081+00:00
-- url     : https://prove2.me/theorems/190171fa-0d13-404a-b02f-50a8b1a92f3b
-- title:
--   Lemma 1 — $\overline W^{(q)}(y)/\overline W^{(q)}(a)\le W^{(q)}(y)/W^{(q)}(a)$
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumptions (no monotone paths, condition (3.3), $E[X_1]>-\infty$), let $q>0$, and let $W^{(q)}$ be its $q$-scale function with antiderivative $\overline W^{(q)}(y)=\int_0^yW^{(q)}(z)\,dz$. Then for every $a>0$ and every $y\in[0,a]$,
--
--   $$\frac{\overline W^{(q)}(y)}{\overline W^{(q)}(a)}\le\frac{W^{(q)}(y)}{W^{(q)}(a)} .$$
--
--   The inequality is used in Lemma 3(ii) to bound the slope of $\bar v_{d^*}$ by $\varphi$.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 6, Lemma 1

import Mathlib
import Definitions.Def_AvramDividend_BailOut_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_BailOut_ScaleFunction

open MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.BailOut

theorem lemma1_scale_ratio {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (Lv : SpectrallyNegativeLevy P 𝓕) (hL : Lv.StandingAssumptions)
    {q : ℝ} (hq : 0 < q)
    {W : ℝ → ℝ} (hW : Lv.triplet.IsScaleFunction q W) :
    ∀ a y : ℝ, 0 < a → y ∈ Set.Icc 0 a → Wbar W y / Wbar W a ≤ W y / W a := by sorry

end AvramDividend.BailOut
